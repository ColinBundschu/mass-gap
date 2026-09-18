import MassGap.Decimationhead
import MassGapChecks.Decimation
/-!
The second check module for `thm:decimation`, the decimated symbol
and the member window.  The decimated symbol reads at the order-five
datum whose tower place is the last key, a positive scalar block
coupled to the head's leading key alone, the tower's deflation the
chain of head diagonal three over the constant `(5, 2)` tail with the
far pivots `85/21, 21/5, 5` inside the ball of radius one about the
deck pivot `4`: the datum's count is the head pivot's, the sum's unit
on both sides through the theorem and decided.  The dominance
comparison is load-bearing: the tower block moved to the lower side
refuses the comparison and the count parts from the head pivot's,
the chain data standing at the recomputed pivots; the ball is
load-bearing: a far diagonal moved to the lower side puts two pivots
off the radius-one ball about the deck pivot and the count parts.
The member window is the plaquette chain of eleven squares over two
letters at the fundamental loops at the squares nought and five,
the two-box loop at nought and the two fundamental loops' pair: the
pair is a slab class, each loop one component, the contents twelve,
thirty-two and twenty-four, and at the bound twenty the tower places
are the two-box loop's position, the head places the unit line with
the two loops', the far places the pair's, the tower vacant at a
bound beyond every content; a class in both ranges, the two-box loop
beside a fundamental loop five squares on, is a tower place with the
far places vacant; the level datum at the contents' diagonal and the
identity gram at the level thirteen reads count three at the whole
datum and at the head pivot alike, through `window_count` and
decided.  Clause (i) at the square window over the two-box loop: the
members' positions, the depth order from the vacuum class the two
positions, the level datum at the loop's term with the identity
gram, the tail recursion's pivots `31/32, 32` at the witness `-1/32`,
and the count the pivots' fold, the sum's unit, through
`window_chain` and decided; the sector frame refuses at the square's
two loops, the fundamental's off the two-box loop's fusion, the depth
order two positions short of three; and the gram's block read is
load-bearing at the cross read, an off-unit gram entry between the two
loops refusing the block read and the off-band read alike.

The binder classification.  `decimated_count`'s `hdom` (the tower
block's dominance at occupied gaps) and `hball` (the far pivots in
the ball) are load-bearing with their committed refusals (`pin161`,
`pin164`); `hk0` is the deflation's frame, its own record at the
vacant tower (`pin171`); `hS`, `hsym`, `hlen`, `hdist`, `hb`,
`hshl`, `hshd`, `hshb`, `hocc` are the datum's, the places' and the
shells' shape reads, `hoff` clause (i)'s off-band read at the shells,
`ht`, `hl` and the splits the chain's certificate, each read in the
proof; `hF` and `hYc` the ball's center data.  `window_count` takes
those binders at the grading's places with `hlen`, `hdist` and `hb`
discharged by the partition reads, `farSh` the far shells as stated
data with `hshl`, `hshd`, `hshb`, `hocc` and `hoff` their shape and
off-band reads, and `hdom` and `hball` load-bearing at the abstract
layer's refusals.  `window_chain`'s `hgram` is load-bearing at the
cross read (`pin181`), `hlen` the sector frame (`pin180`), the
vacuum class the boundary shell (`thm:decimation`(i)), `P`,
`hunitP`, `hix`, `hred` `con:labels`' one reduced shape per label
discharged at the label calculus, `hoff` and `hdist` `def:carrier`'s
index reads, `hdist'` the depth order's distinctness, and the rest
the chain's shape reads.
-/

namespace decimation
open ground lattice fusion elim inertia

private def u : BPair := BPair.unit

/-! The decimated symbol at the order-five datum: the tower place
`4`, the head places `0, 1, 2, 3`, the deflation the `(5, 2)` chain
of head three. -/

private def S5 : Mat :=
  [[⟨5, 1⟩, ⟨3, 1⟩, u, u, ⟨2, 1⟩], [⟨3, 1⟩, ⟨6, 1⟩, ⟨3, 1⟩, u, u],
   [u, ⟨3, 1⟩, ⟨6, 1⟩, ⟨3, 1⟩, u], [u, u, ⟨3, 1⟩, ⟨6, 1⟩, u],
   [⟨2, 1⟩, u, u, u, ⟨2, 1⟩]]
private def D5 : Mat := towerDefl S5 [4] [0, 1, 2, 3]
private def sh4 : List (List Nat) := [[0], [1], [2], [3]]
private def xsB : List greenprod.MatQ :=
  [⟨[[⟨172, 1⟩]], 85⟩, ⟨[[⟨86, 1⟩]], 21⟩, ⟨[[⟨22, 1⟩]], 5⟩, ⟨[[⟨6, 1⟩]], 1⟩]
private def rsB : List greenprod.MatQ :=
  [⟨[[⟨43, 1⟩]], 85⟩, ⟨[[⟨11, 1⟩]], 21⟩, ⟨[[⟨3, 1⟩]], 5⟩]
private def spsB : List ((k : Nat) × Split k) :=
  [⟨1, inertia.oneSplit [⟨172, 1⟩]⟩, ⟨1, inertia.oneSplit [⟨86, 1⟩]⟩,
   ⟨1, inertia.oneSplit [⟨22, 1⟩]⟩, ⟨1, inertia.oneSplit [⟨6, 1⟩]⟩]
private def YB : greenprod.MatQ := ⟨[[⟨5, 1⟩]], 1⟩
private def GB : Mat := [[⟨2, 1⟩]]
private def spKer : Split 1 :=
  ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [], 1, rfl⟩
private def bspsB : List (Split 1 × Split 1) :=
  [(inertia.oneSplit [⟨148, 128⟩], inertia.oneSplit [⟨149, 127⟩]),
   (inertia.oneSplit [⟨36, 32⟩], inertia.oneSplit [⟨37, 31⟩]),
   (spKer, inertia.oneSplit [⟨9, 7⟩])]
private def spS5 : Split 5 := inertia.mkSplit 5 S5
private def spD5 : Split 4 := inertia.mkSplit 4 D5
private def spC5 : Split 4 :=
  inertia.mkSplit 4 (greenprod.assemble (depthchain.slabDiag D5 sh4) (depthchain.slabOff D5 sh4))

theorem pin156 : matOneValue D5
    [[⟨4, 1⟩, ⟨3, 1⟩, u, u], [⟨3, 1⟩, ⟨6, 1⟩, ⟨3, 1⟩, u],
     [u, ⟨3, 1⟩, ⟨6, 1⟩, ⟨3, 1⟩], [u, u, ⟨3, 1⟩, ⟨6, 1⟩]] := by decide +kernel
theorem pin157 : gapPos (selM [4] [4] S5) := by decide +kernel
theorem pin158 : greenprod.tailRead (depthchain.slabDiag D5 sh4) (depthchain.slabOff D5 sh4)
    xsB rsB [1, 1, 1, 1] := by decide +kernel
theorem pin159 : revAt spS5 = revAt (inertia.oneSplit [⟨172, 1⟩]) :=
  decimated_count S5 [4] [0, 1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by decide +kernel) (inertia.oneSplit [⟨2, 1⟩])
    (by decide +kernel) pin157 spS5 (by decide +kernel) spD5 (by decide +kernel)
    sh4 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨[[⟨172, 1⟩]], 85⟩ (xsB.drop 1) rsB [1, 1, 1, 1]
    ⟨1, inertia.oneSplit [⟨172, 1⟩]⟩ (spsB.drop 1) pin158 (by decide +kernel)
    spC5 (by decide +kernel) YB GB 3 1 1 1 spKer bspsB (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem pin160 : revAt spS5 = 0 ∧ revAt (inertia.oneSplit [⟨172, 1⟩]) = 0 := by
  decide +kernel

/-! The dominance comparison isolated: the tower block at the lower
side refuses it, the deflation is the `(5, 2)` chain of head four,
the recomputed pivots `341/85, 85/21, 21/5, 5` with the far three
inside the ball, and the datum's count one against the head pivot's
sum's unit. -/

private def S5n : Mat :=
  [[⟨5, 1⟩, ⟨3, 1⟩, u, u, ⟨2, 1⟩], [⟨3, 1⟩, ⟨6, 1⟩, ⟨3, 1⟩, u, u],
   [u, ⟨3, 1⟩, ⟨6, 1⟩, ⟨3, 1⟩, u], [u, u, ⟨3, 1⟩, ⟨6, 1⟩, u],
   [⟨2, 1⟩, u, u, u, ⟨1, 2⟩]]
private def D5n : Mat := towerDefl S5n [4] [0, 1, 2, 3]
private def xsBn : List greenprod.MatQ :=
  [⟨[[⟨342, 1⟩]], 85⟩, ⟨[[⟨86, 1⟩]], 21⟩, ⟨[[⟨22, 1⟩]], 5⟩, ⟨[[⟨6, 1⟩]], 1⟩]

theorem pin161 : ¬ gapPos (selM [4] [4] S5n) := by decide +kernel
theorem pin162 : greenprod.tailRead (depthchain.slabDiag D5n sh4) (depthchain.slabOff D5n sh4)
    xsBn rsB [1, 1, 1, 1] := by decide +kernel
theorem pin163 : ¬ (revAt (inertia.mkSplit 5 S5n) = revAt (inertia.oneSplit [⟨342, 1⟩])) := by
  decide +kernel

/-! The ball isolated: the last far diagonal at the lower side moves
the chain's pivots to `87/41, 41/9, 9, -1`, the pivots `9` and `-1`
off the radius-one ball about the deck pivot `4` at the ball's
splits, and the datum's count one against the head pivot's sum's
unit. -/

private def S5b : Mat :=
  [[⟨5, 1⟩, ⟨3, 1⟩, u, u, ⟨2, 1⟩], [⟨3, 1⟩, ⟨6, 1⟩, ⟨3, 1⟩, u, u],
   [u, ⟨3, 1⟩, ⟨6, 1⟩, ⟨3, 1⟩, u], [u, u, ⟨3, 1⟩, ⟨1, 2⟩, u],
   [⟨2, 1⟩, u, u, u, ⟨2, 1⟩]]
private def D5b : Mat := towerDefl S5b [4] [0, 1, 2, 3]
private def xsBb : List greenprod.MatQ :=
  [⟨[[⟨88, 1⟩]], 41⟩, ⟨[[⟨42, 1⟩]], 9⟩, ⟨[[⟨10, 1⟩]], 1⟩, ⟨[[⟨1, 2⟩]], 1⟩]
private def rsBb : List greenprod.MatQ :=
  [⟨[[⟨19, 1⟩]], 41⟩, ⟨[[⟨3, 1⟩]], 9⟩, ⟨[[⟨1, 3⟩]], 1⟩]

theorem pin164 : ¬ spectator.ballList YB GB 1 1 (xsBb.drop 1)
    [(inertia.oneSplit [⟨5, 1⟩], inertia.oneSplit [⟨15, 1⟩]),
     (inertia.oneSplit [⟨1, 5⟩], inertia.oneSplit [⟨7, 1⟩]), (spKer, spKer)] := by
  decide +kernel
theorem pin165 : greenprod.tailRead (depthchain.slabDiag D5b sh4) (depthchain.slabOff D5b sh4)
    xsBb rsBb [1, 1, 1, 1] := by decide +kernel
theorem pin166 : ¬ (revAt (inertia.mkSplit 5 S5b) = revAt (inertia.oneSplit [⟨88, 1⟩])) := by
  decide +kernel

/-! The member window: the eleven-square chain over two letters. -/

private def R11 : Region := fiberdec.chainRegion 11
private def FA2 : Data places.Shape := dataA 2
private def plq (i : Nat) : List (Nat × Bool) := ground.getAt [] R11.plaqs i
private def lf : places.Shape := [1, 0]
private def lt : places.Shape := adjchar.theta 2
private def loopL (lab : places.Shape) (i : Nat) : List places.Shape :=
  (List.range R11.links).map (fun l => if (plq i).any (fun e => e.1 == l) then lab else [0, 0])
private def pairL : List places.Shape :=
  (List.range R11.links).map (fun l =>
    if (plq 0).any (fun e => e.1 == l) || (plq 5).any (fun e => e.1 == l) then lf else [0, 0])
private def ixW : List (List places.Shape) := [loopL lf 0, loopL lf 5, loopL lt 0, pairL]

theorem pin167 : carrier.contentN FA2 (loopL lf 0) = 12 ∧ carrier.contentN FA2 (loopL lt 0) = 32
    ∧ carrier.contentN FA2 pairL = 24 := by decide +kernel
theorem pin168 : grading.slabAt FA2 R11 pairL = true
    ∧ grading.slabAt FA2 R11 (loopL lf 0) = false := by decide +kernel
theorem pin169 : towerPlaces FA2 R11 20 ixW 5 = [3] ∧ headPlaces FA2 R11 20 ixW 5 = [0, 1, 2]
    ∧ farPlaces FA2 R11 20 ixW 5 = [4] := by decide +kernel
theorem pin170 : pairpencil.slotDiag FA2 R11 ixW = [0, 12, 12, 32, 24] := by decide +kernel
theorem pin171 : towerPlaces FA2 R11 40 ixW 5 = [] := by decide +kernel

/-! The level datum at the contents' diagonal and the identity gram
at the level thirteen: the tower block `19`, the deflation the
contents' diagonal scaled at the block's square, the head pivot the
head block itself with the far pivot its own block, the ball about
the far pivot at radius one, and the count three on both sides. -/

private def HW : Mat := pairpencil.pencilE [0, 12, 12, 32, 24]
private def SW : Mat := certconstruct.levelDatum HW (idMat 5) 14 1
private def DW : Mat := towerDefl SW [3] [0, 1, 2, 4]
private def shW : List (List Nat) := [List.range 3, [3]]
private def X1W : greenprod.MatQ := ⟨[[⟨1, 4694⟩, u, u], [u, ⟨1, 362⟩, u], [u, u, ⟨1, 362⟩]], 1⟩
private def X2W : greenprod.MatQ := ⟨[[⟨3972, 1⟩]], 1⟩
private def R2W : greenprod.MatQ := ⟨[[u, u, u]], 1⟩
private def s1W : (k : Nat) × Split k :=
  ⟨3, inertia.oneSplit [⟨1, 4694⟩, ⟨1, 362⟩, ⟨1, 362⟩]⟩
private def s2W : (k : Nat) × Split k := ⟨1, inertia.oneSplit [⟨3972, 1⟩]⟩
private def spSW : Split 5 := inertia.mkSplit 5 SW
private def spDW : Split 4 := inertia.mkSplit 4 DW
private def spCW : Split 4 :=
  inertia.mkSplit 4 (greenprod.assemble (depthchain.slabDiag DW shW) (depthchain.slabOff DW shW))

theorem pin172 : matOneValue SW
    [[⟨1, 14⟩, u, u, u, u], [u, ⟨1, 2⟩, u, u, u], [u, u, ⟨1, 2⟩, u, u],
     [u, u, u, ⟨20, 1⟩, u], [u, u, u, u, ⟨12, 1⟩]] := by decide +kernel
theorem pin173 : greenprod.tailRead (depthchain.slabDiag DW shW) (depthchain.slabOff DW shW)
    [X1W, X2W] [R2W] [3, 1] := by decide +kernel
theorem pin174 : revAt spSW = revAt s1W.2 :=
  window_count FA2 R11 20 ixW 5 HW (idMat 5) 14 1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (inertia.oneSplit [⟨20, 1⟩]) (by decide +kernel) (by decide +kernel)
    spSW (by decide +kernel) spDW (by decide +kernel) [[3]] (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    X1W [X2W] [R2W] [3, 1] s1W [s2W] pin173 (by decide +kernel) spCW (by decide +kernel)
    X2W (idMat 1) 1 1 1 1 (inertia.oneSplit [⟨3970, 1⟩])
    [(inertia.oneSplit [⟨2, 1⟩], inertia.oneSplit [⟨2, 1⟩])]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pin175 : revAt spSW = 3 ∧ revAt s1W.2 = 3 := by decide +kernel

/-! Clause (i) at the square window over the two-box loop. -/

private def sqP : List (Nat × Bool) := ground.getAt [] square.plaqs 0
private def loopSq : List places.Shape :=
  (List.range square.links).map (fun l => if sqP.any (fun e => e.1 == l) then lt else [0, 0])
private def ixS : List (List places.Shape) := [loopSq]
private def M2 : Mat := pairpencil.loopMag FA2 [lt]
private def diagS : List Nat := pairpencil.slotDiag FA2 square ixS
private def S2 : Mat := certconstruct.levelDatum (pairpencil.pencilH 1 1 diagS (idMat 2) M2) (idMat 2) 1 2
private def posS : List (List Nat) := memberPos FA2 square ixS 2
private def xsS : List greenprod.MatQ := [⟨[[⟨32, 1⟩]], 32⟩, ⟨[[⟨33, 1⟩]], 1⟩]
private def rsS : List greenprod.MatQ := [⟨[[⟨1, 2⟩]], 32⟩]
private def spsS : List ((k : Nat) × Split k) :=
  [⟨1, inertia.oneSplit [⟨32, 1⟩]⟩, ⟨1, inertia.oneSplit [⟨33, 1⟩]⟩]
private def spMS : Split 2 := inertia.mkSplit 2 S2
private def spCS : Split 2 :=
  inertia.mkSplit 2 (greenprod.assemble
    (depthchain.slabDiag S2 (depthchain.posShells [M2] posS 2 [0]))
    (depthchain.slabOff S2 (depthchain.posShells [M2] posS 2 [0])))

theorem pin176 : posS = [[0], [1]] ∧ diagS = [0, 32]
    ∧ matOneValue S2 [[⟨2, 1⟩, ⟨1, 2⟩], [⟨1, 2⟩, ⟨33, 1⟩]]
    ∧ depthchain.depthOrder [M2] posS 2 [0] = [0, 1] := by decide +kernel
private theorem sqTerms : ∀ T, T ∈ [M2] → sqAt T 2 ∧ matOneValue (transposeM T) T := by
  intro T hT
  rw [eq_of_mem_single hT]
  exact ⟨by decide +kernel, by decide +kernel⟩
private theorem sqLabels : ∀ a, a ∈ ixS → a.all (labelA 2) = true := by
  intro a ha
  rw [eq_of_mem_single ha]
  decide +kernel
private theorem sqOff : ∀ a, a ∈ ixS → (a.any (fun l => !(FA2.eqL l FA2.unit))) = true := by
  intro a ha
  rw [eq_of_mem_single ha]
  decide +kernel
theorem pin177 : greenprod.tailRead
    (depthchain.slabDiag S2 (depthchain.posShells [M2] posS 2 [0]))
    (depthchain.slabOff S2 (depthchain.posShells [M2] posS 2 [0])) xsS rsS [1, 1] := by
  decide +kernel
theorem pin178 : revAt spMS = greenprod.revFold spsS :=
  window_chain FA2 square ixS 2 (by decide) (labelA 2) (labelA_unit 2) sqLabels
    (eqL_labelA 2) sqOff (by decide +kernel) diagS (by decide +kernel) (idMat 2) M2 1 1 1 1 2
    [M2] sqTerms (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) xsS rsS [1, 1] spsS
    pin177 (by decide +kernel) spMS (by decide +kernel) spCS (by decide +kernel)
theorem pin179 : revAt spMS = 0 ∧ greenprod.revFold spsS = 0 := by decide +kernel

/-! The sector frame and the gram's block read isolated at the
square's two loops: the fundamental's loop sits off the two-box
loop's fusion, the depth order from the unit line two positions
short of the order, and an off-unit gram entry between the two loops
refuses the block read with the off-band read beside it. -/

private def loopF : List places.Shape :=
  (List.range square.links).map (fun l => if sqP.any (fun e => e.1 == l) then lf else [0, 0])
private def ixS2 : List (List places.Shape) := [loopF, loopSq]
private def M3 : Mat := pairpencil.loopMag FA2 [lf, lt]
private def posS2 : List (List Nat) := memberPos FA2 square ixS2 3
private def G3 : Mat := [[⟨2, 1⟩, u, u], [u, ⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩, ⟨2, 1⟩]]
private def S3 : Mat :=
  certconstruct.levelDatum (pairpencil.pencilH 1 1 (pairpencil.slotDiag FA2 square ixS2) G3 M3) G3 1 2

theorem pin180 : posS2 = [[0], [1], [2]]
    ∧ depthchain.depthOrder [M3] posS2 3 [0] = [0, 2] := by decide +kernel
theorem pin181 : ¬ pairpencil.gramBlockRead FA2 square 3 ixS2 1 G3
    ∧ depthchain.crossB [M3] posS2 S3 = false := by decide +kernel

/-! The designation at a class in both ranges: the two-box loop at
the square nought beside the fundamental loop at the square five
reads the tower and the slab at the bound twenty, and its position
is a tower place, the far places vacant. -/

private def mixL : List places.Shape :=
  (List.range R11.links).map (fun l =>
    if (plq 0).any (fun e => e.1 == l) then lt
    else if (plq 5).any (fun e => e.1 == l) then lf else [0, 0])

theorem pin182 : grading.towerAt FA2 R11 20 mixL = true ∧ grading.slabAt FA2 R11 mixL = true
    ∧ towerPlaces FA2 R11 20 [mixL] 2 = [1] ∧ farPlaces FA2 R11 20 [mixL] 2 = []
    ∧ headPlaces FA2 R11 20 [mixL] 2 = [0] := by decide +kernel

/-! Clause (ii)'s comparison along the root coordinate: the order-two
polynomial block `[[28 + τ², 2 + τ²], [2 + τ², 40 + τ²]]` reads its
rows' dominance polynomials `26` and `38` on their upper sides over
`[0, 1]` at the bound two, so the evaluated block's gaps sit beyond
the sum's unit at `τ = 1/2`, read through `dom_segment` beside its
own `decide`; the refusals: the off-row entry `30 + τ²` puts the
first row's polynomial at `−2`, and the entry `2 + 3τ²` keeps the
read on `[0, 1]` while the gap at `τ = 4` sits below the unit. -/

private def cfootD : CPair := ⟨BPair.unit, 1⟩
private def ctopD : CPair := ⟨BPair.ofPos 1, 1⟩
private def qD : split.PMat :=
  [[[⟨29, 1⟩, u, ⟨2, 1⟩], [⟨3, 1⟩, u, ⟨2, 1⟩]], [[⟨3, 1⟩, u, ⟨2, 1⟩], [⟨41, 1⟩, u, ⟨2, 1⟩]]]
private def qN : split.PMat :=
  [[[⟨29, 1⟩, u, ⟨2, 1⟩], [⟨31, 1⟩, u, ⟨2, 1⟩]], [[⟨31, 1⟩, u, ⟨2, 1⟩], [⟨41, 1⟩, u, ⟨2, 1⟩]]]
private def qF : split.PMat :=
  [[[⟨29, 1⟩, u, ⟨2, 1⟩], [⟨3, 1⟩, u, ⟨4, 1⟩]], [[⟨3, 1⟩, u, ⟨4, 1⟩], [⟨41, 1⟩, u, ⟨2, 1⟩]]]

theorem pin183 : poly.oneValue (ground.getAt [] (domPolys 0 qD) 0) [⟨27, 1⟩] := by decide +kernel
theorem pin184 : domRead qD cfootD ctopD ⟨3, 1⟩ ⟨2, 1⟩ := by decide +kernel
theorem pin185 : ¬ domRead qN cfootD ctopD ⟨3, 1⟩ ⟨2, 1⟩ := by decide +kernel
theorem pin186 : gapPos (cellcount.evalPC qD ⟨2, 1⟩ 2 2) := by decide +kernel
theorem pin187 : gapPos (cellcount.evalPC qD ⟨2, 1⟩ 2 2) :=
  dom_segment qD 2 cfootD ctopD ⟨3, 1⟩ ⟨2, 1⟩ (by decide +kernel)
    (cellcount.ent_ble (by decide +kernel : cellcount.pShapeAt qD 2 2))
    (BPair.ofPos 1) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
theorem pin188 : ¬ gapPos (cellcount.evalPC qN ⟨2, 1⟩ 2 2) := by decide +kernel
theorem pin189 : domRead qF cfootD ctopD ⟨3, 1⟩ ⟨2, 1⟩ := by decide +kernel
theorem pin190 : ¬ gapPos (cellcount.evalPC qF ⟨5, 1⟩ 1 2) := by decide +kernel

/-! The entry cap binder: the off-row entry `2 + τ² + 1000τ⁴` at the
diagonals `28 + τ²` and `40 + τ²` reads the rows' dominance
polynomials `26 − 1000τ⁴` and `38 − 1000τ⁴` on their upper sides
over `[0, 1/4]` at the bound one quarter, while the clearing two
misreads the quartic key at the point `1/4` and the evaluated gap
sits below the unit; at the clearing four the gap holds. -/

private def qH : split.PMat :=
  [[[⟨29, 1⟩, u, ⟨2, 1⟩], [⟨3, 1⟩, u, ⟨2, 1⟩, u, ⟨1001, 1⟩]],
   [[⟨3, 1⟩, u, ⟨2, 1⟩, u, ⟨1001, 1⟩], [⟨41, 1⟩, u, ⟨2, 1⟩]]]

theorem pin191 : domRead qH cfootD ⟨BPair.ofPos 1, 4⟩ ⟨2, 1⟩ ⟨5, 1⟩ := by decide +kernel
theorem pin192 : ¬ gapPos (cellcount.evalPC qH ⟨2, 1⟩ 4 2) := by decide +kernel
theorem pin193 : gapPos (cellcount.evalPC qH ⟨2, 1⟩ 4 4) := by decide +kernel

end decimation
