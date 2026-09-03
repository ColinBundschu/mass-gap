import MassGap.Momentfold
/-!
The check module for `lem:momentfold`.  The batteries read the
band-one head `ψ = (6, 3, 1)` at the bonds `b = (2, 3)` and the
diagonal `A = (1, 5, 9)`, whose three rows `1·6 ~ 2·3`,
`5·3 ~ 2·6 + 3·1` and `9·1 ~ 3·3` hold, so the recurrence decides and
its two counts read the diagonal's own; the forged last diagonal `8`
parts the last row and refuses it, and two shape refusals cut the
walk's structural conjuncts, one at a bond list one member short and
one at a ground list one member short.

The two weight families are the unit weight `W(k) = 1` and the key
weight `W(k) = k`.  The square fold's displays: at the unit weight
the two bond streams read `45` each against the square stream's `90`;
at the key weight they read `9` and `54` against `63`.  Each display
is decided raw and read again through `fold_sq` at the recurrence's
own read.  The alignment refusal isolates the raised weight's binder:
at the key weight the bond stream at the twice-raised weight reads
`99`, so the sum `108` refuses the square stream's `63`.

The bond fold's displays: at the unit weight the second-bond stream
reads `12` and the down-shifted square stream `21` against the bond
stream's `33`; at the key weight `12` and `3` against `15`.  The
second-bond reduction's displays: at the unit weight `18` and `99`
against `117`; at the key weight the second-bond stream is vacant and
the square stream reads `27` against the raised diagonal's bond
stream `27`.  Each is decided raw and read again through its theorem.

The row reads: the head row `1·6 ~ 2·3` and the first interior row
`5·3 ~ 2·6 + 3·1` decided raw beside their theorem routes, and a
vacancy instance at the key five, every read there off the three
lists.

A second head at partner-signed data — the bonds and the diagonal at
their memberwise swaps, the ground unmoved — decides the recurrence,
its bond stream reads the partner side of `45` and its square stream
the partner side of `90`, and the square fold reads through its
theorem.

The monomial tier reads that head's moments: `mrho` at the vacant,
first and second heights `46`, `11` and `13`, `mc` at `21` and `3`,
`md` at `6`, the boundary square `36` and the far edge at the first
height `2`.  The diagonal `A = (1, 5, 9)` is the linear profile
`4k + 1`, decided, and the forged constant `2` refuses it; the
constant bond `(2, 2)` decides where the head's own bond `(2, 3)`
refuses.  The up-shifted monomial's expansion over the Pascal counts
reads `30` at the second height and the two-step shift `24`; a
constant bond withdraws at `6` on the bonds, at the vacant
second-bond stream, at `22` with the far edge's own `4`, and at `2`
under the down-shift; the down-shifted monomial reads `11` and, at
the vacant power, `46` with the boundary square joining.  The
profile's expansion reads `63` on the squares, `33` on the bonds and
`117` at the raised key, each decided raw and read again through its
theorem, and the forged middle constant `5` refuses the square
expansion at `76` against `63`.

The graded rows read a second head at an occupied quadratic profile,
the ground `ψ = (6, 4, 2)` at the bonds `b = (3, 3)` and the diagonal
`A = (2, 6, 6)`, whose recurrence decides, whose profile is the
quadratic at the partner-signed top constant `2`, the linear `6` and
the constant `2`, and whose bond reads `3`; the unswapped top
constant refuses the profile and the forged bond `(3, 4)` refuses the
constant read.  Its moments are `mrho` at the four lowest heights
`56`, `24`, `32` and `48`, `mc` at those heights `32`, `8`, `8` and
`8`, `md` at the vacant height `12`, the boundary square `36` and the
far edge at the vacant and first heights `4` and `8`.

The rows' values: the square fold's row reads `192` on both sides at
the vacant height and `144` at the first; the reduction's row `204`
at the vacant height and `72` at the first; the bond fold's row `204`
at the vacant height and `144` at the first; the second fold's row
`204` at the vacant height and `552` at the first.  Each display is
decided raw and read again through its theorem.  The bond binder's
refusal forges the square fold's row at the bond datum `4`, whose
right side reads `256` against the row's own `192` and parts it.  The
plain-bond withdrawal reads the vacant second-bond stream at the key
weight and `36` at the vacant power, raw and through its theorem, and
the truncated moment vector at the first degree carries five entries,
the vacant square moment `56` at its head, the vacant bond moment
`32` at the third key and the boundary square `36` at the last.

The truncation cap's tier reads that ground at the unit weight: the
tail from the first key reads `20` and from the third the sum's unit,
and the split at the first key reads the stream's `56` as `36` joined
to `20`; the decay family `(9, 3, 1)` at the sum's unit beyond, whose
consecutive members decay at the pair `1 : 3`, folds to `13` over
five keys, so the fold at the gap `2` reads `26` against the first
member's `27` at `3` and the member at the second key reads `2`
against it, while the turning step at the certificate `1 ≤ 2` and the
turn `16 ≤ 27` reads `16` against `54`; the refusal takes the gap to
the clearing itself, where the fold reads `39` against `27`.

The scale tier reads a third head `ψ = (2, 2, 1)` at the bonds
`b = (2, 2)` and the diagonal `A = (2, 3, 4)`, the linear profile
`k + 2` whose second fold's row reads `22` on both sides, and whose
moments `9`, `6`, `6`, `2` and `4` solve a five-key system beside the
quadratic head's own, the two systems differing in one row and their
data in five, so that the first determinant `4` — refused at the
sum's unit and at its partner, while the second system's determinant
is the sum's unit at its unread column — pins the adjugate identity
at the quadratic head's moment vector and the comparison reads the
moment differences `47`, `18`, `26`, `6` and `32` at that scale
against the adjugate's action on the data difference joined to the
row difference's own action `6`, with two refusals beside it, one at
a difference matrix whose row is one member short and one at a data
difference of no members, each parting the display at an isolated
shape binder.

Clause (v)'s cells: the product width at `x = 5`, `X = 3`, `y = 2`,
`Y = 7` under the caps `3` and `2` reads `1` below `17`, with the
tight cell at `Y = X` reading `9` on both sides and the assembly at
the connected data `1` and `2` reading the sum's unit below `20`;
the block chain decides at four kernels — the two-slab scalar chain
at the unit and key weights, the three-slab chain `(-1, -3, -2)` at
the bonds `(1, 2)` whose key-weighted folds read `-7`, `2` and `5`,
and the two-by-two two-slab chain — each display decided raw and
read again through its theorem, beside a raised-shift refusal whose
fold reads `3`, the unit-sides refusal at the amended head diagonal
whose fold reads `1`, and that amended side list refused as a solve
of the original chain.

The square system's cells: the assembled rows at the quadratic
head's profile pin the committed matrix and data entrywise, the
shape reads land by their theorems, the read lands by the theorem
route beside its decided pin, and the degree floor, the bond datum
and the profile head refuse at their forges.  A second quadratic
fixture, the constant ground `(2, 2, 2)` at the bonds `(2, 2)` and
the diagonal `(2, 4, 2)`, ties to the head's system at a one-row
site datum and a five-member data difference, and the two-scale
comparison lands by the theorem route at the two assembled systems,
both reads the system read's own, and the scale closure reads the
comparison at the datum fold, decided beside its own route.  The commutator's ground read
decides at two symmetric two-by-two data beside its theorem route,
with the symmetry binder refused at an asymmetric datum.  The
refusal tier pins every further probed binder at its forge,
isolated or read at its joint parting: the
comparison's two vector lengths, its coefficient tie, its two
moment ties and its data difference; the action vector's length at
the adjugate pin; the bond and profile lengths across the stream
family at a mismatched ground; the walk-key reads beyond the walk;
the turning step's certificate, turning and positivity data; the
datum read's shape data at the two-slab chain with the walked
length at the chain read's walked-vector frame; the
tail cap's last-member positivity at the vacant span's negative
anchor; and the width arms' caps at the tight fixtures, one forge
per cap.
-/


open ground momentfold

private def psiF : List BPair := [BPair.ofNat 6, BPair.ofNat 3, BPair.ofNat 1]
private def bF : List BPair := [BPair.ofNat 2, BPair.ofNat 3]
private def aF : List BPair := [BPair.ofNat 1, BPair.ofNat 5, BPair.ofNat 9]

private def wOne : Nat → BPair := fun _ => BPair.ofNat 1
private def wKey : Nat → BPair := fun k => BPair.ofNat k

private theorem readF : recRead aF bF psiF := by decide +kernel

example : psiF.length = aF.length := recRead_lenA aF bF psiF readF
example : bF.length + 1 = aF.length := recRead_lenB aF bF psiF readF

private def aForge : List BPair :=
  [BPair.ofNat 1, BPair.ofNat 5, BPair.ofNat 8]

example : ¬ recRead aForge bF psiF := by decide +kernel
example : ¬ recRows BPair.unit aF [BPair.ofNat 2] psiF := by decide +kernel
example : ¬ recRows BPair.unit aF bF [BPair.ofNat 6, BPair.ofNat 3] := by
  decide +kernel

private def sqLo1 : BPair :=
  cStream psiF (fun k => ground.getAt BPair.unit bF k * wOne k)
private def sqHi1 : BPair :=
  cStream psiF (fun k => ground.getAt BPair.unit bF k * wOne (k + 1))
private def sqRho1 : BPair :=
  rhoStream psiF (fun k => ground.getAt BPair.unit aF k * wOne k)

example : sqLo1.oneValue (BPair.ofNat 45) := by decide +kernel
example : sqHi1.oneValue (BPair.ofNat 45) := by decide +kernel
example : (sqLo1 + sqHi1).oneValue (BPair.ofNat 90) := by decide +kernel
example : sqRho1.oneValue (BPair.ofNat 90) := by decide +kernel
example : (sqLo1 + sqHi1).oneValue sqRho1 := by decide +kernel
example : (sqLo1 + sqHi1).oneValue sqRho1 := fold_sq aF bF psiF readF wOne

private def sqLoK : BPair :=
  cStream psiF (fun k => ground.getAt BPair.unit bF k * wKey k)
private def sqHiK : BPair :=
  cStream psiF (fun k => ground.getAt BPair.unit bF k * wKey (k + 1))
private def sqRhoK : BPair :=
  rhoStream psiF (fun k => ground.getAt BPair.unit aF k * wKey k)

example : sqLoK.oneValue (BPair.ofNat 9) := by decide +kernel
example : sqHiK.oneValue (BPair.ofNat 54) := by decide +kernel
example : (sqLoK + sqHiK).oneValue (BPair.ofNat 63) := by decide +kernel
example : sqRhoK.oneValue (BPair.ofNat 63) := by decide +kernel
example : (sqLoK + sqHiK).oneValue sqRhoK := by decide +kernel
example : (sqLoK + sqHiK).oneValue sqRhoK := fold_sq aF bF psiF readF wKey

private def sqSkewK : BPair :=
  cStream psiF (fun k => ground.getAt BPair.unit bF k * wKey (k + 2))

example : sqSkewK.oneValue (BPair.ofNat 99) := by decide +kernel
example : (sqLoK + sqSkewK).oneValue (BPair.ofNat 108) := by decide +kernel
example : ¬ (sqLoK + sqSkewK).oneValue sqRhoK := by decide +kernel

private def bdD1 : BPair :=
  dStream psiF (fun k => ground.getAt BPair.unit bF k * wOne (k + 1))
private def bdR1 : BPair :=
  rhoStream psiF (wShift (fun t => ground.getAt BPair.unit bF t * wOne t))
private def bdC1 : BPair :=
  cStream psiF (fun k => ground.getAt BPair.unit aF k * wOne k)

example : bdD1.oneValue (BPair.ofNat 12) := by decide +kernel
example : bdR1.oneValue (BPair.ofNat 21) := by decide +kernel
example : (bdD1 + bdR1).oneValue (BPair.ofNat 33) := by decide +kernel
example : bdC1.oneValue (BPair.ofNat 33) := by decide +kernel
example : (bdD1 + bdR1).oneValue bdC1 := by decide +kernel
example : (bdD1 + bdR1).oneValue bdC1 := fold_bond aF bF psiF readF wOne

private def bdDK : BPair :=
  dStream psiF (fun k => ground.getAt BPair.unit bF k * wKey (k + 1))
private def bdRK : BPair :=
  rhoStream psiF (wShift (fun t => ground.getAt BPair.unit bF t * wKey t))
private def bdCK : BPair :=
  cStream psiF (fun k => ground.getAt BPair.unit aF k * wKey k)

example : bdDK.oneValue (BPair.ofNat 12) := by decide +kernel
example : bdRK.oneValue (BPair.ofNat 3) := by decide +kernel
example : (bdDK + bdRK).oneValue (BPair.ofNat 15) := by decide +kernel
example : bdCK.oneValue (BPair.ofNat 15) := by decide +kernel
example : (bdDK + bdRK).oneValue bdCK := by decide +kernel
example : (bdDK + bdRK).oneValue bdCK := fold_bond aF bF psiF readF wKey

private def rdD1 : BPair :=
  dStream psiF (fun k => ground.getAt BPair.unit bF (k + 1) * wOne k)
private def rdR1 : BPair :=
  rhoStream psiF (fun k => ground.getAt BPair.unit bF k * wOne k)
private def rdC1 : BPair :=
  cStream psiF (fun k => ground.getAt BPair.unit aF (k + 1) * wOne k)

example : rdD1.oneValue (BPair.ofNat 18) := by decide +kernel
example : rdR1.oneValue (BPair.ofNat 99) := by decide +kernel
example : (rdD1 + rdR1).oneValue (BPair.ofNat 117) := by decide +kernel
example : rdC1.oneValue (BPair.ofNat 117) := by decide +kernel
example : (rdD1 + rdR1).oneValue rdC1 := by decide +kernel
example : (rdD1 + rdR1).oneValue rdC1 := bond2_reduce aF bF psiF readF wOne

private def rdDK : BPair :=
  dStream psiF (fun k => ground.getAt BPair.unit bF (k + 1) * wKey k)
private def rdRK : BPair :=
  rhoStream psiF (fun k => ground.getAt BPair.unit bF k * wKey k)
private def rdCK : BPair :=
  cStream psiF (fun k => ground.getAt BPair.unit aF (k + 1) * wKey k)

example : rdDK.oneValue BPair.unit := by decide +kernel
example : rdRK.oneValue (BPair.ofNat 27) := by decide +kernel
example : (rdDK + rdRK).oneValue (BPair.ofNat 27) := by decide +kernel
example : rdCK.oneValue (BPair.ofNat 27) := by decide +kernel
example : (rdDK + rdRK).oneValue rdCK := by decide +kernel
example : (rdDK + rdRK).oneValue rdCK := bond2_reduce aF bF psiF readF wKey

example : (BPair.ofNat 1 * BPair.ofNat 6).oneValue
    (BPair.ofNat 2 * BPair.ofNat 3) := by decide +kernel
example : (ground.getAt BPair.unit aF 0 * ground.getAt BPair.unit psiF 0).oneValue
    (ground.getAt BPair.unit bF 0 * ground.getAt BPair.unit psiF 1) :=
  rowHead aF bF psiF readF

example : (BPair.ofNat 5 * BPair.ofNat 3).oneValue
    (BPair.ofNat 2 * BPair.ofNat 6 + BPair.ofNat 3 * BPair.ofNat 1) := by
  decide +kernel
example : (ground.getAt BPair.unit aF 1 * ground.getAt BPair.unit psiF 1).oneValue
    (ground.getAt BPair.unit bF 0 * ground.getAt BPair.unit psiF 0
      + ground.getAt BPair.unit bF 1 * ground.getAt BPair.unit psiF 2) :=
  rowAt aF bF psiF readF 0

example : (ground.getAt BPair.unit aF 6 * ground.getAt BPair.unit psiF 6).oneValue
    (ground.getAt BPair.unit bF 5 * ground.getAt BPair.unit psiF 5
      + ground.getAt BPair.unit bF 6 * ground.getAt BPair.unit psiF 7) :=
  rowAt aF bF psiF readF 5

private def bG : List BPair :=
  [(BPair.ofNat 2).swap, (BPair.ofNat 3).swap]
private def aG : List BPair :=
  [(BPair.ofNat 1).swap, (BPair.ofNat 5).swap, (BPair.ofNat 9).swap]

private theorem readG : recRead aG bG psiF := by decide +kernel

private def sqLoG : BPair :=
  cStream psiF (fun k => ground.getAt BPair.unit bG k * wOne k)
private def sqHiG : BPair :=
  cStream psiF (fun k => ground.getAt BPair.unit bG k * wOne (k + 1))
private def sqRhoG : BPair :=
  rhoStream psiF (fun k => ground.getAt BPair.unit aG k * wOne k)

example : sqLoG.oneValue (BPair.ofNat 45).swap := by decide +kernel
example : sqRhoG.oneValue (BPair.ofNat 90).swap := by decide +kernel
example : (sqLoG + sqHiG).oneValue sqRhoG := by decide +kernel
example : (sqLoG + sqHiG).oneValue sqRhoG := fold_sq aG bG psiF readG wOne

private def bC : List BPair := [BPair.ofNat 2, BPair.ofNat 2]

private theorem profF :
    diagProf aF BPair.unit (BPair.ofNat 4) (BPair.ofNat 1) := by decide +kernel

example : ¬ diagProf aF BPair.unit (BPair.ofNat 4) (BPair.ofNat 2) := by
  decide +kernel

private theorem bondC : constBond bC (BPair.ofNat 2) := by decide +kernel

example : ¬ constBond bF (BPair.ofNat 2) := by decide +kernel

example : (mrho psiF 0).oneValue (BPair.ofNat 46) := by decide +kernel
example : (mrho psiF 1).oneValue (BPair.ofNat 11) := by decide +kernel
example : (mrho psiF 2).oneValue (BPair.ofNat 13) := by decide +kernel
example : (mc psiF 0).oneValue (BPair.ofNat 21) := by decide +kernel
example : (mc psiF 1).oneValue (BPair.ofNat 3) := by decide +kernel
example : (md psiF 0).oneValue (BPair.ofNat 6) := by decide +kernel
example : (bSq psiF).oneValue (BPair.ofNat 36) := by decide +kernel
example : (edgeAt psiF 1).oneValue (BPair.ofNat 2) := by decide +kernel

private def profRead2 : BPair :=
  BPair.unit * BPair.ofNat (2 * 2)
    + (BPair.ofNat 4 * BPair.ofNat 2 + BPair.ofNat 1)

example : (ground.getAt BPair.unit aF 2).oneValue profRead2 := by decide +kernel
example : (ground.getAt BPair.unit aF 2).oneValue profRead2 :=
  prof_at aF BPair.unit (BPair.ofNat 4) (BPair.ofNat 1) profF 2 (by decide +kernel)

example : (ground.getAt BPair.unit bC 1).oneValue (BPair.ofNat 2) := by
  decide +kernel
example : (ground.getAt BPair.unit bC 1).oneValue (BPair.ofNat 2) :=
  bond_at bC (BPair.ofNat 2) bondC 1 (by decide +kernel)

private def gOne : Nat → BPair := fun _ => BPair.ofNat 1

private def shC : BPair :=
  cStream psiF (fun k => gOne k * ground.bpow (BPair.ofNat (k + 1)) 2)
private def shCsum : BPair :=
  ground.bsum (fun t => BPair.ofNat (ground.pasc 2 t)
    * cStream psiF (fun k => gOne k * ground.bpow (BPair.ofNat k) t))
    (List.range 3)

example : shC.oneValue (BPair.ofNat 30) := by decide +kernel
example : shCsum.oneValue (BPair.ofNat 30) := by decide +kernel
example : shC.oneValue shCsum := by decide +kernel
example : shC.oneValue shCsum := cShift1 psiF gOne 2

private def shD : BPair :=
  dStream psiF (fun k => gOne k * ground.bpow (BPair.ofNat (k + 2)) 2)
private def shDsum : BPair :=
  ground.bsum (fun t => BPair.ofNat (ground.pasc 2 t)
    * (ground.bpow (BPair.ofNat 2) (2 - t)
      * dStream psiF (fun k => gOne k * ground.bpow (BPair.ofNat k) t)))
    (List.range 3)

example : shD.oneValue (BPair.ofNat 24) := by decide +kernel
example : shDsum.oneValue (BPair.ofNat 24) := by decide +kernel
example : shD.oneValue shDsum := by decide +kernel
example : shD.oneValue shDsum := dShift2 psiF gOne 2

private def vKey : Nat → BPair := fun k => ground.bpow (BPair.ofNat k) 1

private def cbLo : BPair :=
  cStream psiF (fun k => ground.getAt BPair.unit bC k * vKey k)

example : cbLo.oneValue (BPair.ofNat 6) := by decide +kernel
example : (BPair.ofNat 2 * cStream psiF vKey).oneValue (BPair.ofNat 6) := by
  decide +kernel
example : cbLo.oneValue (BPair.ofNat 2 * cStream psiF vKey) := by decide +kernel
example : cbLo.oneValue (BPair.ofNat 2 * cStream psiF vKey) :=
  cBond bC psiF (BPair.ofNat 2) bondC rfl vKey

private def dbUp : BPair :=
  dStream psiF (fun k => ground.getAt BPair.unit bC (k + 1) * vKey k)

example : dbUp.oneValue BPair.unit := by decide +kernel
example : (BPair.ofNat 2 * dStream psiF vKey).oneValue BPair.unit := by
  decide +kernel
example : dbUp.oneValue (BPair.ofNat 2 * dStream psiF vKey) := by decide +kernel
example : dbUp.oneValue (BPair.ofNat 2 * dStream psiF vKey) :=
  dBondUp bC psiF (BPair.ofNat 2) bondC rfl vKey

private def rbLo : BPair :=
  rhoStream psiF (fun k => ground.getAt BPair.unit bC k * vKey k)
private def rbEdge : BPair :=
  BPair.ofNat 2 * (ground.bpow (BPair.ofNat 2) 1
    * (ground.getAt BPair.unit psiF 2 * ground.getAt BPair.unit psiF 2))

example : rbLo.oneValue (BPair.ofNat 18) := by decide +kernel
example : rbEdge.oneValue (BPair.ofNat 4) := by decide +kernel
example : (rbLo + rbEdge).oneValue (BPair.ofNat 22) := by decide +kernel
example : (BPair.ofNat 2 * rhoStream psiF vKey).oneValue (BPair.ofNat 22) := by
  decide +kernel
example : (rbLo + rbEdge).oneValue (BPair.ofNat 2 * rhoStream psiF vKey) := by
  decide +kernel
example : (rbLo + rbEdge).oneValue (BPair.ofNat 2 * rhoStream psiF vKey) :=
  rhoBond bC psiF (BPair.ofNat 2) bondC rfl vKey

private def wcLo : BPair :=
  rhoStream psiF (wShift (fun t => ground.getAt BPair.unit bC t * vKey t))

example : wcLo.oneValue (BPair.ofNat 2) := by decide +kernel
example : (BPair.ofNat 2 * rhoStream psiF (wShift vKey)).oneValue
    (BPair.ofNat 2) := by decide +kernel
example : wcLo.oneValue (BPair.ofNat 2 * rhoStream psiF (wShift vKey)) := by
  decide +kernel
example : wcLo.oneValue (BPair.ofNat 2 * rhoStream psiF (wShift vKey)) :=
  wCollapse bC psiF (BPair.ofNat 2) bondC rfl vKey

private def wmS : BPair :=
  rhoStream psiF (wShift (fun t => ground.bpow (BPair.ofNat (t + 1)) 1))

example : wmS.oneValue (BPair.ofNat 11) := by decide +kernel
example : wmS.oneValue (mrho psiF 1) := by decide +kernel
example : wmS.oneValue (mrho psiF 1) := wMono_succ psiF 0

private def wmZ : BPair :=
  rhoStream psiF (wShift (fun t => ground.bpow (BPair.ofNat (t + 1)) 0))

example : wmZ.oneValue (BPair.ofNat 10) := by decide +kernel
example : (wmZ + bSq psiF).oneValue (BPair.ofNat 46) := by decide +kernel
example : (wmZ + bSq psiF).oneValue (mrho psiF 0) := by decide +kernel
example : (wmZ + bSq psiF).oneValue (mrho psiF 0) := wMono_zero psiF

private def prR : BPair :=
  rhoStream psiF (fun k => ground.getAt BPair.unit aF k
    * ground.bpow (BPair.ofNat k) 1)
private def prRead : BPair :=
  BPair.unit * mrho psiF 3
    + (BPair.ofNat 4 * mrho psiF 2 + BPair.ofNat 1 * mrho psiF 1)

example : prR.oneValue (BPair.ofNat 63) := by decide +kernel
example : prRead.oneValue (BPair.ofNat 63) := by decide +kernel
example : prR.oneValue prRead := by decide +kernel
example : prR.oneValue prRead :=
  profRho aF psiF BPair.unit (BPair.ofNat 4) (BPair.ofNat 1) profF rfl 1

private def pcR : BPair :=
  cStream psiF (fun k => ground.getAt BPair.unit aF k
    * ground.bpow (BPair.ofNat k) 0)
private def pcRead : BPair :=
  BPair.unit * mc psiF 2
    + (BPair.ofNat 4 * mc psiF 1 + BPair.ofNat 1 * mc psiF 0)

example : pcR.oneValue (BPair.ofNat 33) := by decide +kernel
example : pcRead.oneValue (BPair.ofNat 33) := by decide +kernel
example : pcR.oneValue pcRead := by decide +kernel
example : pcR.oneValue pcRead :=
  profC aF psiF BPair.unit (BPair.ofNat 4) (BPair.ofNat 1) profF rfl 0

private def pcU : BPair :=
  cStream psiF (fun k => ground.getAt BPair.unit aF (k + 1)
    * ground.bpow (BPair.ofNat k) 0)
private def pcURead : BPair :=
  BPair.unit * mc psiF 2
    + ((BPair.unit + BPair.unit + BPair.ofNat 4) * mc psiF 1
      + (BPair.unit + BPair.ofNat 4 + BPair.ofNat 1) * mc psiF 0)

example : pcU.oneValue (BPair.ofNat 117) := by decide +kernel
example : pcURead.oneValue (BPair.ofNat 117) := by decide +kernel
example : pcU.oneValue pcURead := by decide +kernel
example : pcU.oneValue pcURead :=
  profCUp aF psiF BPair.unit (BPair.ofNat 4) (BPair.ofNat 1) profF rfl 0

private def prForge : BPair :=
  BPair.unit * mrho psiF 3
    + (BPair.ofNat 5 * mrho psiF 2 + BPair.ofNat 1 * mrho psiF 1)

example : prForge.oneValue (BPair.ofNat 76) := by decide +kernel
example : ¬ prR.oneValue prForge := by decide +kernel

namespace momentfold

/-- The quadratic head's fixtures, published for the sibling check
modules reading the same head. -/
def psiH : List BPair := [BPair.ofNat 6, BPair.ofNat 4, BPair.ofNat 2]
def bH : List BPair := [BPair.ofNat 3, BPair.ofNat 3]
def aH : List BPair := [BPair.ofNat 2, BPair.ofNat 6, BPair.ofNat 6]
def pH2 : BPair := (BPair.ofNat 2).swap

theorem readH : recRead aH bH psiH := by decide +kernel
theorem profH : diagProf aH pH2 (BPair.ofNat 6) (BPair.ofNat 2) := by
  decide +kernel
theorem bondH : constBond bH (BPair.ofNat 3) := by decide +kernel

end momentfold

example : ¬ diagProf aH (BPair.ofNat 2) (BPair.ofNat 6) (BPair.ofNat 2) := by
  decide +kernel

private def bHforge : List BPair := [BPair.ofNat 3, BPair.ofNat 4]

example : ¬ constBond bHforge (BPair.ofNat 3) := by decide +kernel

example : (mrho psiH 0).oneValue (BPair.ofNat 56) := by decide +kernel
example : (mrho psiH 1).oneValue (BPair.ofNat 24) := by decide +kernel
example : (mrho psiH 2).oneValue (BPair.ofNat 32) := by decide +kernel
example : (mrho psiH 3).oneValue (BPair.ofNat 48) := by decide +kernel
example : (mc psiH 0).oneValue (BPair.ofNat 32) := by decide +kernel
example : (mc psiH 1).oneValue (BPair.ofNat 8) := by decide +kernel
example : (mc psiH 2).oneValue (BPair.ofNat 8) := by decide +kernel
example : (mc psiH 3).oneValue (BPair.ofNat 8) := by decide +kernel
example : (md psiH 0).oneValue (BPair.ofNat 12) := by decide +kernel
example : (bSq psiH).oneValue (BPair.ofNat 36) := by decide +kernel
example : (edgeAt psiH 0).oneValue (BPair.ofNat 4) := by decide +kernel
example : (edgeAt psiH 1).oneValue (BPair.ofNat 8) := by decide +kernel

private def faLo0 : BPair :=
  (BPair.ofNat 2).swap * mrho psiH 2
    + (BPair.ofNat 6 * mrho psiH 1 + BPair.ofNat 2 * mrho psiH 0)
private def faHi0 : BPair :=
  BPair.ofNat 3 * mc psiH 0
    + BPair.ofNat 3 * ground.bsum
        (fun t => BPair.ofNat (ground.pasc 0 t) * mc psiH t) (List.range 1)

example : faLo0.oneValue (BPair.ofNat 192) := by decide +kernel
example : faHi0.oneValue (BPair.ofNat 192) := by decide +kernel
example : faLo0.oneValue faHi0 := by decide +kernel
example : faLo0.oneValue faHi0 :=
  fa_row aH bH psiH (BPair.ofNat 2).swap (BPair.ofNat 6) (BPair.ofNat 2)
    (BPair.ofNat 3) readH profH bondH 0

private def faForge0 : BPair :=
  BPair.ofNat 4 * mc psiH 0
    + BPair.ofNat 4 * ground.bsum
        (fun t => BPair.ofNat (ground.pasc 0 t) * mc psiH t) (List.range 1)

example : faForge0.oneValue (BPair.ofNat 256) := by decide +kernel
example : ¬ faLo0.oneValue faForge0 := by decide +kernel

private def faLo1 : BPair :=
  (BPair.ofNat 2).swap * mrho psiH 3
    + (BPair.ofNat 6 * mrho psiH 2 + BPair.ofNat 2 * mrho psiH 1)
private def faHi1 : BPair :=
  BPair.ofNat 3 * mc psiH 1
    + BPair.ofNat 3 * ground.bsum
        (fun t => BPair.ofNat (ground.pasc 1 t) * mc psiH t) (List.range 2)

example : faLo1.oneValue (BPair.ofNat 144) := by decide +kernel
example : faHi1.oneValue (BPair.ofNat 144) := by decide +kernel
example : faLo1.oneValue faHi1 := by decide +kernel
example : faLo1.oneValue faHi1 :=
  fa_row aH bH psiH (BPair.ofNat 2).swap (BPair.ofNat 6) (BPair.ofNat 2)
    (BPair.ofNat 3) readH profH bondH 1

private def drLo0 : BPair :=
  BPair.ofNat 3 * md psiH 0 + BPair.ofNat 3 * mrho psiH 0
private def drHi0 : BPair :=
  (BPair.ofNat 2).swap * mc psiH 2
    + (((BPair.ofNat 2).swap + (BPair.ofNat 2).swap + BPair.ofNat 6)
        * mc psiH 1
      + ((BPair.ofNat 2).swap + BPair.ofNat 6 + BPair.ofNat 2) * mc psiH 0)
    + BPair.ofNat 3 * edgeAt psiH 0

example : drLo0.oneValue (BPair.ofNat 204) := by decide +kernel
example : drHi0.oneValue (BPair.ofNat 204) := by decide +kernel
example : drLo0.oneValue drHi0 := by decide +kernel
example : drLo0.oneValue drHi0 :=
  d_row aH bH psiH (BPair.ofNat 2).swap (BPair.ofNat 6) (BPair.ofNat 2)
    (BPair.ofNat 3) readH profH bondH 0

private def drLo1 : BPair :=
  BPair.ofNat 3 * md psiH 1 + BPair.ofNat 3 * mrho psiH 1
private def drHi1 : BPair :=
  (BPair.ofNat 2).swap * mc psiH 3
    + (((BPair.ofNat 2).swap + (BPair.ofNat 2).swap + BPair.ofNat 6)
        * mc psiH 2
      + ((BPair.ofNat 2).swap + BPair.ofNat 6 + BPair.ofNat 2) * mc psiH 1)
    + BPair.ofNat 3 * edgeAt psiH 1

example : drLo1.oneValue (BPair.ofNat 72) := by decide +kernel
example : drHi1.oneValue (BPair.ofNat 72) := by decide +kernel
example : drLo1.oneValue drHi1 := by decide +kernel
example : drLo1.oneValue drHi1 :=
  d_row aH bH psiH (BPair.ofNat 2).swap (BPair.ofNat 6) (BPair.ofNat 2)
    (BPair.ofNat 3) readH profH bondH 1

private def fbHi0 : BPair :=
  (BPair.ofNat 2).swap * mc psiH 2
    + (BPair.ofNat 6 * mc psiH 1 + BPair.ofNat 2 * mc psiH 0)
    + BPair.ofNat 3 * bSq psiH

example : fbHi0.oneValue (BPair.ofNat 204) := by decide +kernel
example : drLo0.oneValue fbHi0 := by decide +kernel
example : drLo0.oneValue fbHi0 :=
  fb_row_zero aH bH psiH (BPair.ofNat 2).swap (BPair.ofNat 6) (BPair.ofNat 2)
    (BPair.ofNat 3) readH profH bondH

example : drHi0.oneValue fbHi0 := by decide +kernel
example : drHi0.oneValue fbHi0 :=
  fbd_row_zero aH bH psiH (BPair.ofNat 2).swap (BPair.ofNat 6) (BPair.ofNat 2)
    (BPair.ofNat 3) readH profH bondH

private def fbsLo0 : BPair :=
  BPair.ofNat 3 * ground.bsum (fun t => BPair.ofNat (ground.pasc 1 t)
      * (ground.bpow (BPair.ofNat 2) (1 - t) * md psiH t)) (List.range 2)
    + BPair.ofNat 3 * mrho psiH 1
private def fbsHi0 : BPair :=
  ground.bsum (fun s => BPair.ofNat (ground.pasc 1 s)
    * ((BPair.ofNat 2).swap * mc psiH (s + 2)
      + (BPair.ofNat 6 * mc psiH (s + 1) + BPair.ofNat 2 * mc psiH s)))
    (List.range 2)

example : fbsLo0.oneValue (BPair.ofNat 144) := by decide +kernel
example : fbsHi0.oneValue (BPair.ofNat 144) := by decide +kernel
example : fbsLo0.oneValue fbsHi0 := by decide +kernel
example : fbsLo0.oneValue fbsHi0 :=
  fb_row_succ aH bH psiH (BPair.ofNat 2).swap (BPair.ofNat 6) (BPair.ofNat 2)
    (BPair.ofNat 3) readH profH bondH 0

private def fbdLo0 : BPair :=
  BPair.ofNat 3 * mrho psiH 1
    + ground.bsum (fun t => BPair.ofNat (ground.pasc 1 t)
        * (ground.bpow (BPair.ofNat 2) (1 - t)
          * ((BPair.ofNat 2).swap * mc psiH (t + 2)
            + (((BPair.ofNat 2).swap + (BPair.ofNat 2).swap + BPair.ofNat 6)
                * mc psiH (t + 1)
              + ((BPair.ofNat 2).swap + BPair.ofNat 6 + BPair.ofNat 2)
                * mc psiH t)
            + BPair.ofNat 3 * edgeAt psiH t))) (List.range 2)
private def fbdHi0 : BPair :=
  ground.bsum (fun s => BPair.ofNat (ground.pasc 1 s)
    * ((BPair.ofNat 2).swap * mc psiH (s + 2)
      + (BPair.ofNat 6 * mc psiH (s + 1) + BPair.ofNat 2 * mc psiH s)))
    (List.range 2)
    + ground.bsum (fun t => BPair.ofNat (ground.pasc 1 t)
      * (ground.bpow (BPair.ofNat 2) (1 - t)
        * (BPair.ofNat 3 * mrho psiH t))) (List.range 2)

example : fbdLo0.oneValue (BPair.ofNat 552) := by decide +kernel
example : fbdHi0.oneValue (BPair.ofNat 552) := by decide +kernel
example : fbdLo0.oneValue fbdHi0 := by decide +kernel
example : fbdLo0.oneValue fbdHi0 :=
  fbd_row_succ aH bH psiH (BPair.ofNat 2).swap (BPair.ofNat 6) (BPair.ofNat 2)
    (BPair.ofNat 3) readH profH bondH 0

private def vKeyH : Nat → BPair := fun k => ground.bpow (BPair.ofNat k) 1
private def vOneH : Nat → BPair := fun k => ground.bpow (BPair.ofNat k) 0

private def dbLoK : BPair :=
  dStream psiH (fun k => ground.getAt BPair.unit bH k * vKeyH k)

example : dbLoK.oneValue BPair.unit := by decide +kernel
example : (BPair.ofNat 3 * dStream psiH vKeyH).oneValue BPair.unit := by
  decide +kernel
example : dbLoK.oneValue (BPair.ofNat 3 * dStream psiH vKeyH) := by
  decide +kernel
example : dbLoK.oneValue (BPair.ofNat 3 * dStream psiH vKeyH) :=
  dBond bH psiH (BPair.ofNat 3) bondH rfl vKeyH

private def dbLo1 : BPair :=
  dStream psiH (fun k => ground.getAt BPair.unit bH k * vOneH k)

example : dbLo1.oneValue (BPair.ofNat 36) := by decide +kernel
example : (BPair.ofNat 3 * dStream psiH vOneH).oneValue (BPair.ofNat 36) := by
  decide +kernel
example : dbLo1.oneValue (BPair.ofNat 3 * dStream psiH vOneH) := by
  decide +kernel
example : dbLo1.oneValue (BPair.ofNat 3 * dStream psiH vOneH) :=
  dBond bH psiH (BPair.ofNat 3) bondH rfl vOneH

example : (momVec psiH 1).length = 5 := rfl
example : (ground.getAt BPair.unit (momVec psiH 1) 0).oneValue
    (BPair.ofNat 56) := by decide +kernel
example : (ground.getAt BPair.unit (momVec psiH 1) 2).oneValue
    (BPair.ofNat 32) := by decide +kernel
example : (ground.getAt BPair.unit (momVec psiH 1) 4).oneValue
    (BPair.ofNat 36) := by decide +kernel

example : (tailStream psiH wOne 1).oneValue (BPair.ofNat 20) := by decide +kernel
example : (tailStream psiH wOne 3).oneValue BPair.unit := by decide +kernel

private def tailLo : BPair := rhoStream psiH wOne
private def tailHi : BPair :=
  ground.bsum (fun k => wOne k
    * (ground.getAt BPair.unit psiH k * ground.getAt BPair.unit psiH k))
    (List.range 1)
    + tailStream psiH wOne 1

example : tailLo.oneValue (BPair.ofNat 56) := by decide +kernel
example : tailHi.oneValue (BPair.ofNat 56) := by decide +kernel
example : tailLo.oneValue tailHi := by decide +kernel
example : tailLo.oneValue tailHi := tail_split psiH wOne 1

private def decayF : Nat → BPair
  | 0 => BPair.ofNat 9
  | 1 => BPair.ofNat 3
  | 2 => BPair.ofNat 1
  | _ + 3 => BPair.unit

private theorem decayPos : ∀ m : Nat, BPair.unit ≤ decayF m
  | 0 => by decide +kernel
  | 1 => by decide +kernel
  | 2 => by decide +kernel
  | _ + 3 => ground.leB_refl BPair.unit

private theorem decayStep : ∀ m : Nat, 0 ≤ m →
    (decayF (m + 1)).scale 3 ≤ (decayF m).scale 1
  | 0, _ => by decide +kernel
  | 1, _ => by decide +kernel
  | 2, _ => by decide +kernel
  | _ + 3, _ =>
    ground.leB_congr (ground.unitScale 3) (ground.unitScale 1)
      (ground.leB_refl BPair.unit)

private def decayFold : BPair :=
  ground.bsum (fun t => decayF (0 + t)) (List.range 5)

example : (decayFold.scale 2).oneValue (BPair.ofNat 26) := by decide +kernel
example : ((decayF 0).scale 3).oneValue (BPair.ofNat 27) := by decide +kernel
example : decayFold.scale 2 ≤ (decayF 0).scale 3 := by decide +kernel
example : decayFold.scale 2 ≤ (decayF 0).scale 3 :=
  tail_capped decayF 0 4 1 2 3 rfl (ground.leB_refl BPair.unit)
    (fun m hm _ => decayStep m hm)

example : ¬ (decayFold.scale 3 ≤ (decayF 0).scale 3) := by decide +kernel

example : ((decayF 2).scale 2).oneValue (BPair.ofNat 2) := by decide +kernel
example : (decayF 2).scale 2 ≤ (decayF 0).scale 3 := by decide +kernel
example : (decayF 2).scale 2 ≤ (decayF 0).scale 3 :=
  edge_capped decayF 0 2 (by decide +kernel) 1 2 3 rfl
    (fun k _ _ => decayPos k) (fun k hk _ => decayStep k hk)

private theorem turnCert :
    (BPair.ofNat 1).scale (1 * 1) ≤ (BPair.ofNat 2).scale (1 * 1) := by
  decide +kernel
private theorem turnRead : (BPair.ofNat 8).scale (1 * 1 * 2)
    ≤ (BPair.ofNat 9).scale (1 * 1 * 3) := by decide +kernel
example : ((BPair.ofNat 8 * BPair.ofNat 1).scale 2).oneValue
    (BPair.ofNat 16) := by decide +kernel
example : ((BPair.ofNat 9 * BPair.ofNat 2).scale 3).oneValue
    (BPair.ofNat 54) := by decide +kernel
example : (BPair.ofNat 8 * BPair.ofNat 1).scale 2
    ≤ (BPair.ofNat 9 * BPair.ofNat 2).scale 3 := by decide +kernel
example : (BPair.ofNat 8 * BPair.ofNat 1).scale 2
    ≤ (BPair.ofNat 9 * BPair.ofNat 2).scale 3 :=
  turn_step (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 8) (BPair.ofNat 9)
    1 1 3 2 turnCert turnRead (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def psiG2 : List BPair := [BPair.ofNat 2, BPair.ofNat 2, BPair.ofNat 1]
private def bG2 : List BPair := [BPair.ofNat 2, BPair.ofNat 2]
private def aG2 : List BPair := [BPair.ofNat 2, BPair.ofNat 3, BPair.ofNat 4]

private theorem readG2 : recRead aG2 bG2 psiG2 := by decide +kernel
private theorem profG2 :
    diagProf aG2 BPair.unit (BPair.ofNat 1) (BPair.ofNat 2) := by decide +kernel
private theorem bondG2 : constBond bG2 (BPair.ofNat 2) := by decide +kernel

example : (mrho psiG2 0).oneValue (BPair.ofNat 9) := by decide +kernel
example : (mrho psiG2 1).oneValue (BPair.ofNat 6) := by decide +kernel
example : (mc psiG2 0).oneValue (BPair.ofNat 6) := by decide +kernel
example : (mc psiG2 1).oneValue (BPair.ofNat 2) := by decide +kernel
example : (bSq psiG2).oneValue (BPair.ofNat 4) := by decide +kernel
example : (edgeAt psiG2 0).oneValue (BPair.ofNat 1) := by decide +kernel

private def fbdG2Lo : BPair :=
  BPair.unit * mc psiG2 2
    + ((BPair.unit + BPair.unit + BPair.ofNat 1) * mc psiG2 1
      + (BPair.unit + BPair.ofNat 1 + BPair.ofNat 2) * mc psiG2 0)
    + BPair.ofNat 2 * edgeAt psiG2 0
private def fbdG2Hi : BPair :=
  BPair.unit * mc psiG2 2
    + (BPair.ofNat 1 * mc psiG2 1 + BPair.ofNat 2 * mc psiG2 0)
    + BPair.ofNat 2 * bSq psiG2

example : fbdG2Lo.oneValue (BPair.ofNat 22) := by decide +kernel
example : fbdG2Hi.oneValue (BPair.ofNat 22) := by decide +kernel
example : fbdG2Lo.oneValue fbdG2Hi := by decide +kernel
example : fbdG2Lo.oneValue fbdG2Hi :=
  fbd_row_zero aG2 bG2 psiG2 BPair.unit (BPair.ofNat 1) (BPair.ofNat 2)
    (BPair.ofNat 2) readG2 profG2 bondG2

private def sysH : elim.Mat :=
  [[BPair.ofNat 1, BPair.unit, BPair.unit, BPair.unit, BPair.unit],
   [BPair.unit, BPair.ofNat 1, BPair.unit, BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit, BPair.ofNat 1, BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit, BPair.unit, BPair.unit, BPair.ofNat 1],
   [BPair.unit, BPair.unit, BPair.ofNat 4, (BPair.ofNat 4).swap,
    (BPair.ofNat 3).swap]]
private def rhsH : List BPair :=
  [BPair.ofNat 56, BPair.ofNat 24, BPair.ofNat 32, BPair.ofNat 36,
   (BPair.ofNat 12).swap]
private def sysG : elim.Mat :=
  [[BPair.ofNat 1, BPair.unit, BPair.unit, BPair.unit, BPair.unit],
   [BPair.unit, BPair.ofNat 1, BPair.unit, BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit, BPair.ofNat 1, BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit, BPair.unit, BPair.unit, BPair.ofNat 1],
   [BPair.unit, BPair.unit, BPair.ofNat 1, BPair.unit,
    (BPair.ofNat 2).swap]]
private def rhsG : List BPair :=
  [BPair.ofNat 9, BPair.ofNat 6, BPair.ofNat 6, BPair.ofNat 4,
   (BPair.ofNat 2).swap]
private def dSys : elim.Mat :=
  [[BPair.unit, BPair.unit, BPair.unit, BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit, BPair.unit, BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit, BPair.unit, BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit, BPair.unit, BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit, BPair.ofNat 3, (BPair.ofNat 4).swap,
    (BPair.ofNat 1).swap]]
private def dRhs : List BPair :=
  [BPair.ofNat 47, BPair.ofNat 18, BPair.ofNat 26, BPair.ofNat 32,
   (BPair.ofNat 10).swap]

private theorem cohH : poly.oneValue (elim.matVec sysH (momVec psiH 1)) rhsH := by
  decide +kernel
private theorem cohG :
    poly.oneValue (elim.matVec sysG (momVec psiG2 1)) rhsG := by decide +kernel
private theorem tieSys : elim.matOneValue sysH (elim.matAdd sysG dSys) := by
  decide +kernel
private theorem tieRhs : poly.oneValue rhsH (poly.add rhsG dRhs) := by
  decide +kernel
private theorem sqH : elim.sqAt sysH 5 := by decide +kernel
private theorem sqG : elim.sqAt sysG 5 := by decide +kernel
private theorem sqD : elim.sqAt dSys 5 := by decide +kernel

example : dRhs.length = 5 := rfl

set_option maxRecDepth 100000 in
example : (elim.detL sysH).oneValue (BPair.ofNat 4) := by decide +kernel
example : ¬ (elim.detL sysH).oneValue BPair.unit := by decide +kernel
example : ¬ (elim.detL sysH).oneValue (BPair.ofNat 4).swap := by decide +kernel
example : (elim.detL sysG).oneValue BPair.unit := by decide +kernel
example : ¬ (elim.detL sysG).oneValue (BPair.ofNat 1) := by decide +kernel

private def pinLo : List BPair :=
  elim.matVec (elim.matMul (elim.adjM sysH) sysH) (momVec psiH 1)
private def pinHi : List BPair :=
  elim.vecScale (elim.detL sysH) (momVec psiH 1)

example : poly.oneValue pinLo pinHi := by decide +kernel
example : poly.oneValue pinLo pinHi :=
  inertia.det_pin (n := 5) sysH sqH (momVec psiH 1) rfl

example : poly.oneValue (elim.matVec dSys (momVec psiG2 1))
    [BPair.unit, BPair.unit, BPair.unit, BPair.unit, BPair.ofNat 6] := by
  decide +kernel

private def cmpLo : List BPair :=
  elim.vecScale (elim.detL sysH)
    (elim.vecAdd (momVec psiH 1) ((momVec psiG2 1).map BPair.swap))
private def cmpHi : List BPair :=
  elim.matVec (elim.adjM sysH)
    (elim.vecAdd dRhs ((elim.matVec dSys (momVec psiG2 1)).map BPair.swap))

example : poly.oneValue cmpLo cmpHi := by decide +kernel
example : poly.oneValue cmpLo cmpHi :=
  scale_compare (n := 5) sysH sysG dSys sqH sqG sqD tieSys
    (momVec psiH 1) (momVec psiG2 1) rhsH rhsG dRhs cohH cohG tieRhs
    rfl rfl rfl

private def narrowS : elim.Mat := [[BPair.unit]]
private def narrowSp : elim.Mat := [[BPair.ofNat 1]]
private def narrowD : elim.Mat := [([] : List BPair)]
private def narrowV : List BPair := [BPair.ofNat 5]
private def narrowVp : List BPair := [BPair.ofNat 1]
private def narrowW : List BPair := [BPair.unit]
private def narrowWp : List BPair := [BPair.ofNat 1]
private def narrowDw : List BPair := [(BPair.ofNat 1).swap]

example : elim.sqAt narrowS 1 := by decide +kernel
example : elim.sqAt narrowSp 1 := by decide +kernel
example : elim.matOneValue narrowS (elim.matAdd narrowSp narrowD) := by
  decide +kernel
example : poly.oneValue (elim.matVec narrowS narrowV) narrowW := by decide +kernel
example : poly.oneValue (elim.matVec narrowSp narrowVp) narrowWp := by
  decide +kernel
example : poly.oneValue narrowW (poly.add narrowWp narrowDw) := by decide +kernel
example : narrowV.length = 1 := rfl
example : narrowVp.length = 1 := rfl
example : narrowDw.length = 1 := rfl
example : ¬ elim.sqAt narrowD 1 := by decide +kernel
example : ¬ poly.oneValue
    (elim.vecScale (elim.detL narrowS)
      (elim.vecAdd narrowV (narrowVp.map BPair.swap)))
    (elim.matVec (elim.adjM narrowS)
      (elim.vecAdd narrowDw
        ((elim.matVec narrowD narrowVp).map BPair.swap))) := by decide +kernel

private def bareS : elim.Mat := [[BPair.ofNat 1]]
private def bareSp : elim.Mat := [[BPair.ofNat 2]]
private def bareD : elim.Mat := [[(BPair.ofNat 1).swap]]
private def bareV : List BPair := [BPair.ofNat 2]
private def bareVp : List BPair := [BPair.ofNat 1]
private def bareW : List BPair := [BPair.ofNat 2]
private def bareWp : List BPair := [BPair.ofNat 2]
private def bareDw : List BPair := ([] : List BPair)

example : elim.sqAt bareS 1 := by decide +kernel
example : elim.sqAt bareSp 1 := by decide +kernel
example : elim.sqAt bareD 1 := by decide +kernel
example : elim.matOneValue bareS (elim.matAdd bareSp bareD) := by decide +kernel
example : poly.oneValue (elim.matVec bareS bareV) bareW := by decide +kernel
example : poly.oneValue (elim.matVec bareSp bareVp) bareWp := by decide +kernel
example : poly.oneValue bareW (poly.add bareWp bareDw) := by decide +kernel
example : bareV.length = 1 := rfl
example : bareVp.length = 1 := rfl
example : ¬ (bareDw.length = 1) := by decide +kernel
example : ¬ poly.oneValue
    (elim.vecScale (elim.detL bareS)
      (elim.vecAdd bareV (bareVp.map BPair.swap)))
    (elim.matVec (elim.adjM bareS)
      (elim.vecAdd bareDw
        ((elim.matVec bareD bareVp).map BPair.swap))) := by decide +kernel

/- The shared-order binders' refusals: the two vector lengths and
the coefficients' tie, each isolated at a forged datum with every
further binder pinned and the conclusion refused. -/

private def flvS : elim.Mat := [[BPair.ofNat 2]]
private def flvSp : elim.Mat := [[BPair.ofNat 1]]
private def flvD : elim.Mat := [[BPair.ofNat 1]]
private def flvW : List BPair := [BPair.unit]
private def flvWp : List BPair := [BPair.ofNat 1]
private def flvDw : List BPair := [(BPair.ofNat 1).swap]

example : elim.sqAt flvS 1 := by decide +kernel
example : elim.sqAt flvSp 1 := by decide +kernel
example : elim.sqAt flvD 1 := by decide +kernel
example : elim.matOneValue flvS (elim.matAdd flvSp flvD) := by
  decide +kernel
example : poly.oneValue (elim.matVec flvS ([] : List BPair)) flvW := by
  decide +kernel
example : poly.oneValue (elim.matVec flvSp [BPair.ofNat 1]) flvWp := by
  decide +kernel
example : poly.oneValue flvW (poly.add flvWp flvDw) := by decide +kernel
example : ¬ (([] : List BPair).length = 1) := by decide +kernel
example : ¬ poly.oneValue
    (elim.vecScale (elim.detL flvS)
      (elim.vecAdd ([] : List BPair) ([BPair.ofNat 1].map BPair.swap)))
    (elim.matVec (elim.adjM flvS)
      (elim.vecAdd flvDw
        ((elim.matVec flvD [BPair.ofNat 1]).map BPair.swap))) := by
  decide +kernel

private def flpW : List BPair := [BPair.ofNat 6]
private def flpWp : List BPair := [BPair.unit]
private def flpDw : List BPair := [BPair.ofNat 6]

example : poly.oneValue (elim.matVec flvS [BPair.ofNat 3]) flpW := by
  decide +kernel
example : poly.oneValue (elim.matVec flvSp ([] : List BPair)) flpWp := by
  decide +kernel
example : poly.oneValue flpW (poly.add flpWp flpDw) := by decide +kernel
example : ¬ poly.oneValue
    (elim.vecScale (elim.detL flvS)
      (elim.vecAdd [BPair.ofNat 3] (([] : List BPair).map BPair.swap)))
    (elim.matVec (elim.adjM flvS)
      (elim.vecAdd flpDw
        ((elim.matVec flvD ([] : List BPair)).map BPair.swap))) := by
  decide +kernel

private def ftieD : elim.Mat := [[BPair.ofNat 5]]
private def ftieW : List BPair := [BPair.ofNat 6]
private def ftieWp : List BPair := [BPair.ofNat 1]
private def ftieDw : List BPair := [BPair.ofNat 5]

example : elim.sqAt ftieD 1 := by decide +kernel
example : ¬ elim.matOneValue flvS (elim.matAdd flvSp ftieD) := by
  decide +kernel
example : poly.oneValue (elim.matVec flvS [BPair.ofNat 3]) ftieW := by
  decide +kernel
example : poly.oneValue (elim.matVec flvSp [BPair.ofNat 1]) ftieWp := by
  decide +kernel
example : poly.oneValue ftieW (poly.add ftieWp ftieDw) := by decide +kernel
example : ¬ poly.oneValue
    (elim.vecScale (elim.detL flvS)
      (elim.vecAdd [BPair.ofNat 3] ([BPair.ofNat 1].map BPair.swap)))
    (elim.matVec (elim.adjM flvS)
      (elim.vecAdd ftieDw
        ((elim.matVec ftieD [BPair.ofNat 1]).map BPair.swap))) := by
  decide +kernel

/- The bond and profile length binders' refusals at a four-deep
ground against the two-member data. -/

private def psi4 : List BPair :=
  [BPair.ofNat 6, BPair.ofNat 4, BPair.ofNat 2, BPair.ofNat 1]

example : ¬ (bC.length + 1 = psi4.length) := by decide +kernel
example : ¬ (cStream psi4 (fun k => ground.getAt BPair.unit bC k
    * ground.bpow (BPair.ofNat k) 0)).oneValue
    (BPair.ofNat 2 * mc psi4 0) := by decide +kernel

private def aP : List BPair := [BPair.ofNat 1, BPair.ofNat 5]

example : diagProf aP BPair.unit (BPair.ofNat 4) (BPair.ofNat 1) := by
  decide +kernel
example : ¬ (psi4.length = aP.length) := by decide +kernel
example : ¬ (rhoStream psi4
    (fun k => ground.getAt BPair.unit aP k
      * ground.bpow (BPair.ofNat k) 1)).oneValue
    (BPair.unit * mrho psi4 3
      + (BPair.ofNat 4 * mrho psi4 2 + BPair.ofNat 1 * mrho psi4 1)) := by
  decide +kernel

/- The turning step's certificate and turning binders, each isolated
at its forge with the further binders pinned; the positivity binders,
the clause's stated gram frame, read load-bearing at two joint
partings, the turning pair off the unit at one forge and the
certificate pair at the other, the conclusion refused at each. -/

example : ¬ ((BPair.ofNat 3).scale (1 * 1)
    ≤ (BPair.ofNat 1).scale (1 * 1)) := by decide +kernel
example : (BPair.ofNat 1).scale (1 * 1 * 2)
    ≤ (BPair.ofNat 2).scale (1 * 1 * 1) := by decide +kernel
example : ¬ ((BPair.ofNat 1 * BPair.ofNat 3).scale 2
    ≤ (BPair.ofNat 2 * BPair.ofNat 1).scale 1) := by decide +kernel

example : (BPair.ofNat 1).scale (1 * 1) ≤ (BPair.ofNat 1).scale (1 * 1) := by
  decide +kernel
example : ¬ ((BPair.ofNat 3).scale (1 * 1 * 2)
    ≤ (BPair.ofNat 1).scale (1 * 1 * 1)) := by decide +kernel
example : ¬ ((BPair.ofNat 3 * BPair.ofNat 1).scale 2
    ≤ (BPair.ofNat 1 * BPair.ofNat 1).scale 1) := by decide +kernel

example : (BPair.ofNat 2).scale (1 * 1) ≤ (BPair.ofNat 3).scale (1 * 1) := by
  decide +kernel
example : ((BPair.ofNat 5).swap).scale (1 * 1 * 1)
    ≤ ((BPair.ofNat 5).swap).scale (1 * 1 * 1) := by decide +kernel
example : ¬ (BPair.unit ≤ (BPair.ofNat 5).swap) := by decide +kernel
example : ¬ (((BPair.ofNat 5).swap * BPair.ofNat 2).scale 1
    ≤ ((BPair.ofNat 5).swap * BPair.ofNat 3).scale 1) := by decide +kernel

example : ((BPair.ofNat 2).swap).scale (1 * 1)
    ≤ ((BPair.ofNat 1).swap).scale (1 * 1) := by decide +kernel
example : (BPair.ofNat 1).scale (1 * 1 * 1)
    ≤ (BPair.ofNat 5).scale (1 * 1 * 1) := by decide +kernel
example : ¬ (BPair.unit ≤ (BPair.ofNat 1).swap) := by decide +kernel
example : ¬ ((BPair.ofNat 1 * (BPair.ofNat 2).swap).scale 1
    ≤ (BPair.ofNat 5 * (BPair.ofNat 1).swap).scale 1) := by decide +kernel

/- The tail cap's last-member positivity, isolated at the vacant
span's negative anchor, the anchor's own negativity the read
above. -/

example : ¬ ((ground.bsum (fun _ => (BPair.ofNat 5).swap)
    (List.range 1)).scale 1
    ≤ ((BPair.ofNat 5).swap).scale 2) := by decide +kernel

/- The single-region datum read at the two-slab chain: the stream
read's decided anchor beside the theorem route; the bond count
parted short refuses with the walked length holding, and the two
part jointly at the combined forge; the walked length reads
lem:greenprod (iv)'s walked-vector frame through the chain read,
its two partings satisfying at the padded reads with the bond
count's long parting beside them. -/

private def drD : List BPair := [BPair.ofNat 2, BPair.ofNat 1]
private def drD3 : List BPair :=
  [BPair.ofNat 2, BPair.ofNat 1, BPair.ofNat 3]
private def drO : List BPair := [BPair.ofNat 1]
private def drO5 : List BPair := [BPair.ofNat 1, BPair.ofNat 5]
private def drU : List BPair := [BPair.ofNat 1, BPair.ofNat 2]
private def drU3 : List BPair :=
  [BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3]
private def drRead (d o v : List BPair) : BPair :=
  rhoStream v (ground.getAt BPair.unit d)
    + BPair.ofNat 2 * cStream v (ground.getAt BPair.unit o)
private def drForm (d o : List BPair) (v : List BPair) : BPair :=
  inertia.quadForm
    (greenprod.assemble (d.map (fun a => [[a]]))
      (o.map (fun b => [[b]]))) v

example : (drRead drD drO drU).oneValue (BPair.ofNat 10) := by
  decide +kernel
example : (drForm drD drO drU).oneValue (drRead drD drO drU) :=
  datum_read drD drO drU rfl rfl
example : ¬ ((drForm drD3 drO drU3).oneValue
    (drRead drD3 drO drU3)) := by decide +kernel
example : ¬ ((drForm drD drO5 drU3).oneValue
    (drRead drD drO5 drU3)) := by decide +kernel
example : (drForm drD drO drU3).oneValue (drRead drD drO drU3) := by
  decide +kernel
example : (drForm drD3 drO5 drU).oneValue (drRead drD3 drO5 drU) := by
  decide +kernel
example : (drForm drD drO5 drU).oneValue (drRead drD drO5 drU) := by
  decide +kernel

/- The square system at the fixtures: the assembled rows pin the
committed matrices, the read lands by the theorem route, and the
degree floor with the bond datum refuse at their forges. -/

example : elim.matOneValue
    (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2) (BPair.ofNat 3))
    sysH := by decide +kernel
example : poly.oneValue (momRhs psiH (BPair.ofNat 3) 1) rhsH := by
  decide +kernel
example : (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2)
    (BPair.ofNat 3)).length = 5 :=
  momSys_len 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2) (BPair.ofNat 3)
    (Nat.le_refl 1)
example : elim.rowsLen 5
    (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2) (BPair.ofNat 3)) :=
  momSys_rowsLen 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2) (BPair.ofNat 3)

private theorem sysReadH : poly.oneValue
    (elim.matVec (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2)
      (BPair.ofNat 3)) (momVec psiH 1))
    (momRhs psiH (BPair.ofNat 3) 1) :=
  momSys_read aH bH psiH pH2 (BPair.ofNat 6) (BPair.ofNat 2)
    (BPair.ofNat 3) 1 readH profH bondH (Nat.le_refl 1)

example : poly.oneValue
    (elim.matVec (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2)
      (BPair.ofNat 3)) (momVec psiH 1))
    (momRhs psiH (BPair.ofNat 3) 1) := by decide +kernel

example : ¬ (1 ≤ 0) := by decide +kernel
example : ¬ poly.oneValue
    (elim.matVec (momSys 0 pH2 (BPair.ofNat 6) (BPair.ofNat 2)
      (BPair.ofNat 3)) (momVec psiH 0))
    (momRhs psiH (BPair.ofNat 3) 0) := by decide +kernel
example : ¬ constBond bHforge (BPair.ofNat 3) := by decide +kernel
example : ¬ poly.oneValue
    (elim.matVec (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2)
      (BPair.ofNat 4)) (momVec psiH 1))
    (momRhs psiH (BPair.ofNat 3) 1) := by decide +kernel

/- The two-scale comparison at two quadratic systems: the second
fixture's recurrence at its own profile, the site datum and the
data difference tied, and the comparison landed by the theorem
route beside its decided read. -/

private def psiQ : List BPair :=
  [BPair.ofNat 2, BPair.ofNat 2, BPair.ofNat 2]
private def bQ : List BPair := [BPair.ofNat 2, BPair.ofNat 2]
private def aQ : List BPair :=
  [BPair.ofNat 2, BPair.ofNat 4, BPair.ofNat 2]

private theorem readQ : recRead aQ bQ psiQ := by decide +kernel
private theorem profQ :
    diagProf aQ pH2 (BPair.ofNat 4) (BPair.ofNat 2) := by decide +kernel
private theorem bondQ : constBond bQ (BPair.ofNat 2) := by decide +kernel

private theorem sysReadQ : poly.oneValue
    (elim.matVec (momSys 1 pH2 (BPair.ofNat 4) (BPair.ofNat 2)
      (BPair.ofNat 2)) (momVec psiQ 1))
    (momRhs psiQ (BPair.ofNat 2) 1) :=
  momSys_read aQ bQ psiQ pH2 (BPair.ofNat 4) (BPair.ofNat 2)
    (BPair.ofNat 2) 1 readQ profQ bondQ (Nat.le_refl 1)

private def dSysQ : elim.Mat :=
  [[BPair.unit, BPair.unit, BPair.unit, BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit, BPair.unit, BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit, BPair.unit, BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit, BPair.unit, BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit, BPair.ofNat 2, BPair.unit,
    (BPair.ofNat 1).swap]]
private def dRhsQ : List BPair :=
  [BPair.ofNat 44, BPair.ofNat 12, BPair.ofNat 24, BPair.ofNat 32,
   (BPair.ofNat 4).swap]

set_option maxRecDepth 100000 in
private theorem sqMomH : elim.sqAt
    (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2) (BPair.ofNat 3)) 5 := by
  decide +kernel
set_option maxRecDepth 100000 in
private theorem sqMomQ : elim.sqAt
    (momSys 1 pH2 (BPair.ofNat 4) (BPair.ofNat 2) (BPair.ofNat 2)) 5 := by
  decide +kernel
example : elim.sqAt dSysQ 5 := by decide +kernel
set_option maxRecDepth 100000 in
private theorem tieSysQ : elim.matOneValue
    (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2) (BPair.ofNat 3))
    (elim.matAdd (momSys 1 pH2 (BPair.ofNat 4) (BPair.ofNat 2)
      (BPair.ofNat 2)) dSysQ) := by decide +kernel
private theorem tieRhsQ : poly.oneValue (momRhs psiH (BPair.ofNat 3) 1)
    (poly.add (momRhs psiQ (BPair.ofNat 2) 1) dRhsQ) := by decide +kernel

set_option maxRecDepth 1000000 in
example : poly.oneValue
    (elim.vecScale
      (elim.detL (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2)
        (BPair.ofNat 3)))
      (elim.vecAdd (momVec psiH 1) ((momVec psiQ 1).map BPair.swap)))
    (elim.matVec
      (elim.adjM (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2)
        (BPair.ofNat 3)))
      (elim.vecAdd dRhsQ
        ((elim.matVec dSysQ (momVec psiQ 1)).map BPair.swap))) := by
  decide +kernel
example : poly.oneValue
    (elim.vecScale
      (elim.detL (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2)
        (BPair.ofNat 3)))
      (elim.vecAdd (momVec psiH 1) ((momVec psiQ 1).map BPair.swap)))
    (elim.matVec
      (elim.adjM (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2)
        (BPair.ofNat 3)))
      (elim.vecAdd dRhsQ
        ((elim.matVec dSysQ (momVec psiQ 1)).map BPair.swap))) :=
  scale_compare (n := 5)
    (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2) (BPair.ofNat 3))
    (momSys 1 pH2 (BPair.ofNat 4) (BPair.ofNat 2) (BPair.ofNat 2))
    dSysQ sqMomH sqMomQ (by decide +kernel) tieSysQ
    (momVec psiH 1) (momVec psiQ 1)
    (momRhs psiH (BPair.ofNat 3) 1) (momRhs psiQ (BPair.ofNat 2) 1)
    dRhsQ sysReadH sysReadQ tieRhsQ rfl rfl rfl

/- The scale closure at the two quadratic systems' fixture: the
datum fold's comparison decided and landed by the theorem route,
the binders the comparison's own. -/

private def cWQ : List BPair :=
  [BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3, BPair.ofNat 4,
   BPair.ofNat 5]

set_option maxRecDepth 1000000 in
example : (elim.detL (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2)
      (BPair.ofNat 3))
    * (elim.dotP cWQ (momVec psiH 1)
      + (elim.dotP cWQ (momVec psiQ 1)).swap)).oneValue
    (elim.dotP cWQ
      (elim.matVec
        (elim.adjM (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2)
          (BPair.ofNat 3)))
        (elim.vecAdd dRhsQ
          ((elim.matVec dSysQ (momVec psiQ 1)).map BPair.swap)))) := by
  decide +kernel
example : (elim.detL (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2)
      (BPair.ofNat 3))
    * (elim.dotP cWQ (momVec psiH 1)
      + (elim.dotP cWQ (momVec psiQ 1)).swap)).oneValue
    (elim.dotP cWQ
      (elim.matVec
        (elim.adjM (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2)
          (BPair.ofNat 3)))
        (elim.vecAdd dRhsQ
          ((elim.matVec dSysQ (momVec psiQ 1)).map BPair.swap)))) :=
  datum_close (n := 5)
    (momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2) (BPair.ofNat 3))
    (momSys 1 pH2 (BPair.ofNat 4) (BPair.ofNat 2) (BPair.ofNat 2))
    dSysQ sqMomH sqMomQ (by decide +kernel) tieSysQ
    (momVec psiH 1) (momVec psiQ 1)
    (momRhs psiH (BPair.ofNat 3) 1) (momRhs psiQ (BPair.ofNat 2) 1)
    dRhsQ cWQ sysReadH sysReadQ tieRhsQ rfl rfl rfl


/- The commutator's ground read at two symmetric data, with the
symmetry binder's refusal at an asymmetric second datum. -/

private def cgM : elim.Mat :=
  [[BPair.ofNat 2, BPair.ofNat 1], [BPair.ofNat 1, BPair.ofNat 3]]
private def cgN : elim.Mat :=
  [[BPair.ofNat 1, BPair.ofNat 4], [BPair.ofNat 4, BPair.ofNat 2]]
private def cgA : elim.Mat :=
  [[BPair.ofNat 1, BPair.ofNat 4], [BPair.unit, BPair.ofNat 2]]
private def cgPsi : List BPair := [BPair.ofNat 1, BPair.ofNat 2]

example : elim.matOneValue (elim.transposeM cgM) cgM := by decide +kernel
example : elim.matOneValue (elim.transposeM cgN) cgN := by decide +kernel
example : (elim.dotP cgPsi (elim.matVec cgM (elim.matVec cgN cgPsi))).oneValue
    (elim.dotP cgPsi (elim.matVec cgN (elim.matVec cgM cgPsi))) := by
  decide +kernel
example : (elim.dotP cgPsi (elim.matVec cgM (elim.matVec cgN cgPsi))).oneValue
    (elim.dotP cgPsi (elim.matVec cgN (elim.matVec cgM cgPsi))) :=
  commGround (n := 2) cgM cgN (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) cgPsi rfl
example : ¬ elim.matOneValue (elim.transposeM cgA) cgA := by decide +kernel
example : ¬ (elim.dotP cgPsi
    (elim.matVec cgM (elim.matVec cgA cgPsi))).oneValue
    (elim.dotP cgPsi (elim.matVec cgA (elim.matVec cgM cgPsi))) := by
  decide +kernel


/- The further binders' refusals: the two moment ties and the data
difference, the action's vector length, the bond and profile
lengths across the stream family, the walk-key reads beyond the
walk, and the width arms' caps, each isolated at its forge. -/
private def fOne : List BPair := [BPair.ofNat 1]
private def fuD : elim.Mat := [[BPair.unit]]
private def foS : elim.Mat := [[BPair.ofNat 1]]

-- scale_compare hv forged (w wrong)
example : ¬ poly.oneValue (elim.matVec foS [BPair.ofNat 5])
    [BPair.ofNat 10] := by decide +kernel
example : poly.oneValue (elim.matVec foS fOne) fOne := by decide +kernel
example : poly.oneValue [BPair.ofNat 10]
    (poly.add fOne [BPair.ofNat 9]) := by decide +kernel
example : elim.sqAt fuD 1 := by decide +kernel
example : elim.matOneValue foS (elim.matAdd foS fuD) := by decide +kernel
example : ¬ poly.oneValue
    (elim.vecScale (elim.detL foS)
      (elim.vecAdd [BPair.ofNat 5] (fOne.map BPair.swap)))
    (elim.matVec (elim.adjM foS)
      (elim.vecAdd [BPair.ofNat 9]
        ((elim.matVec fuD fOne).map BPair.swap))) := by decide +kernel

-- scale_compare hv' forged (w' wrong)
example : poly.oneValue (elim.matVec foS [BPair.ofNat 5])
    [BPair.ofNat 5] := by decide +kernel
example : ¬ poly.oneValue (elim.matVec foS fOne) [BPair.ofNat 2] := by
  decide +kernel
example : poly.oneValue [BPair.ofNat 5]
    (poly.add [BPair.ofNat 2] [BPair.ofNat 3]) := by decide +kernel
example : ¬ poly.oneValue
    (elim.vecScale (elim.detL foS)
      (elim.vecAdd [BPair.ofNat 5] (fOne.map BPair.swap)))
    (elim.matVec (elim.adjM foS)
      (elim.vecAdd [BPair.ofNat 3]
        ((elim.matVec fuD fOne).map BPair.swap))) := by decide +kernel

-- scale_compare hdw forged
example : ¬ poly.oneValue [BPair.ofNat 5]
    (poly.add fOne [BPair.ofNat 7]) := by decide +kernel
example : ¬ poly.oneValue
    (elim.vecScale (elim.detL foS)
      (elim.vecAdd [BPair.ofNat 5] (fOne.map BPair.swap)))
    (elim.matVec (elim.adjM foS)
      (elim.vecAdd [BPair.ofNat 7]
        ((elim.matVec fuD fOne).map BPair.swap))) := by decide +kernel

-- det_pin hz forged (z too long)
private def twfoS : elim.Mat := [[BPair.ofNat 2]]
example : elim.sqAt twfoS 1 := by decide +kernel
example : ¬ (([BPair.ofNat 3, BPair.ofNat 4] : List BPair).length = 1) := by
  decide +kernel
example : ¬ poly.oneValue
    (elim.matVec (elim.matMul (elim.adjM twfoS) twfoS)
      [BPair.ofNat 3, BPair.ofNat 4])
    (elim.vecScale (elim.detL twfoS) [BPair.ofNat 3, BPair.ofNat 4]) := by
  decide +kernel


-- the bond family's hlen at the four-deep ground
private def fbC : List BPair := [BPair.ofNat 2, BPair.ofNat 2]
private def fpsi4X : List BPair :=
  [BPair.ofNat 6, BPair.ofNat 4, BPair.ofNat 2, BPair.ofNat 1]
private def fvOne : Nat → BPair := fun _ => BPair.ofNat 1

example : ¬ (dStream fpsi4X (fun k => ground.getAt BPair.unit fbC (k + 1)
    * fvOne k)).oneValue (BPair.ofNat 2 * dStream fpsi4X fvOne) := by
  decide +kernel
example : ¬ (rhoStream fpsi4X (fun k => ground.getAt BPair.unit fbC k
    * fvOne k)
    + BPair.ofNat 2 * (fvOne (fpsi4X.length - 1)
      * (ground.getAt BPair.unit fpsi4X (fpsi4X.length - 1)
        * ground.getAt BPair.unit fpsi4X (fpsi4X.length - 1)))).oneValue
    (BPair.ofNat 2 * rhoStream fpsi4X fvOne) := by decide +kernel
example : ¬ (rhoStream fpsi4X
    (wShift (fun t => ground.getAt BPair.unit fbC t * fvOne t))).oneValue
    (BPair.ofNat 2 * rhoStream fpsi4X (wShift fvOne)) := by decide +kernel

-- profC / profCUp hlen at the two-member profile
private def faP : List BPair := [BPair.ofNat 1, BPair.ofNat 5]
example : ¬ (cStream fpsi4X
    (fun k => ground.getAt BPair.unit faP k
      * ground.bpow (BPair.ofNat k) 0)).oneValue
    (BPair.unit * mc fpsi4X 2
      + (BPair.ofNat 4 * mc fpsi4X 1 + BPair.ofNat 1 * mc fpsi4X 0)) := by
  decide +kernel
example : ¬ (cStream fpsi4X
    (fun k => ground.getAt BPair.unit faP (k + 1)
      * ground.bpow (BPair.ofNat k) 0)).oneValue
    (BPair.unit * mc fpsi4X 2
      + ((BPair.unit + BPair.unit + BPair.ofNat 4) * mc fpsi4X 1
        + (BPair.unit + BPair.ofNat 4 + BPair.ofNat 1) * mc fpsi4X 0)) := by
  decide +kernel

example : ¬ (ground.getAt BPair.unit fbC 2).oneValue (BPair.ofNat 2) := by
  decide +kernel


-- momSys_read hp forged (wrong profile head)
example : ¬ diagProf [BPair.ofNat 2, BPair.ofNat 6, BPair.ofNat 6]
    BPair.unit (BPair.ofNat 6) (BPair.ofNat 2) := by decide +kernel
example : ¬ poly.oneValue
    (elim.matVec (momSys 1 BPair.unit (BPair.ofNat 6) (BPair.ofNat 2)
      (BPair.ofNat 3))
      (momVec [BPair.ofNat 6, BPair.ofNat 4, BPair.ofNat 2] 1))
    (momRhs [BPair.ofNat 6, BPair.ofNat 4, BPair.ofNat 2]
      (BPair.ofNat 3) 1) := by decide +kernel

-- dBond hlen at the five-deep ground
private def gbC : List BPair := [BPair.ofNat 2, BPair.ofNat 2]
private def gpsi5 : List BPair :=
  [BPair.ofNat 6, BPair.ofNat 4, BPair.ofNat 2, BPair.ofNat 1,
   BPair.ofNat 1]
private def gvOne : Nat → BPair := fun _ => BPair.ofNat 1
example : ¬ (gbC.length + 1 = gpsi5.length) := by decide +kernel
example : ¬ (dStream gpsi5 (fun k => ground.getAt BPair.unit gbC k
    * gvOne k)).oneValue (BPair.ofNat 2 * dStream gpsi5 gvOne) := by
  decide +kernel

-- prof_at hk with the F profile
private def gaF : List BPair := [BPair.ofNat 1, BPair.ofNat 5, BPair.ofNat 9]
example : diagProf gaF BPair.unit (BPair.ofNat 4) (BPair.ofNat 1) := by
  decide +kernel
example : ¬ (ground.getAt BPair.unit gaF 3).oneValue
    (BPair.unit * BPair.ofNat (3 * 3)
      + (BPair.ofNat 4 * BPair.ofNat 3 + BPair.ofNat 1)) := by
  decide +kernel

-- prodWidth cap refusals
example : windowsep.mag (BPair.ofNat 1) ≤ BPair.ofNat 1 := by decide +kernel
example : ¬ (windowsep.mag (BPair.ofNat 2) ≤ BPair.ofNat 1) := by
  decide +kernel
example : ¬ (windowsep.mag (BPair.ofNat 9 * BPair.ofNat 2
      + (BPair.ofNat 1 * BPair.ofNat 1).swap)
    ≤ BPair.ofNat 1 * windowsep.mag (BPair.ofNat 9 + (BPair.ofNat 1).swap)
      + BPair.ofNat 1
        * windowsep.mag (BPair.ofNat 2 + (BPair.ofNat 1).swap)) := by
  decide +kernel
example : windowsep.mag (BPair.ofNat 3) ≤ BPair.ofNat 3 := by decide +kernel
example : ¬ (windowsep.mag (BPair.ofNat 9 * BPair.ofNat 2
      + (BPair.ofNat 3 * BPair.ofNat 1).swap)
    ≤ BPair.ofNat 2 * windowsep.mag (BPair.ofNat 9 + (BPair.ofNat 3).swap)
      + BPair.ofNat 1
        * windowsep.mag (BPair.ofNat 2 + (BPair.ofNat 1).swap)) := by
  decide +kernel

-- assemble_close cap refusals, fOne per cap at the tight fixture
private def gr1 : BPair := BPair.ofNat 9
private def gr2 : BPair := BPair.ofNat 2
private def gr1p : BPair := BPair.ofNat 1
private def gr2p : BPair := BPair.ofNat 1
example : ¬ (windowsep.mag ((gr1 * gr2 + BPair.unit)
      + (gr1p * gr2p + BPair.unit).swap)
    ≤ BPair.ofNat 1 * windowsep.mag (gr1 + gr1p.swap)
      + (BPair.ofNat 1 * windowsep.mag (gr2 + gr2p.swap)
        + (BPair.unit + BPair.unit))) := by decide +kernel
example : ¬ (windowsep.mag ((gr1 * gr2 + BPair.unit)
      + (gr1p * gr2p + BPair.unit).swap)
    ≤ BPair.ofNat 2 * windowsep.mag (gr1 + gr1p.swap)
      + (BPair.unit * windowsep.mag (gr2 + gr2p.swap)
        + (BPair.unit + BPair.unit))) := by decide +kernel
example : ¬ (windowsep.mag ((gr1 * gr2 + BPair.unit)
      + (gr1p * gr2p + BPair.unit).swap)
    ≤ BPair.ofNat 2 * BPair.ofNat 7
      + (BPair.ofNat 1 * windowsep.mag (gr2 + gr2p.swap)
        + (BPair.unit + BPair.unit))) := by decide +kernel
example : ¬ (windowsep.mag ((gr1 * gr2 + BPair.unit)
      + (gr1p * gr2p + BPair.unit).swap)
    ≤ BPair.ofNat 2 * windowsep.mag (gr1 + gr1p.swap)
      + (BPair.ofNat 1 * BPair.unit + (BPair.unit + BPair.unit))) := by
  decide +kernel
example : ¬ (windowsep.mag ((gr1 * gr2 + BPair.ofNat 3)
      + (gr1p * gr2p + BPair.unit).swap)
    ≤ BPair.ofNat 2 * windowsep.mag (gr1 + gr1p.swap)
      + (BPair.ofNat 1 * windowsep.mag (gr2 + gr2p.swap)
        + (BPair.ofNat 1 + BPair.unit))) := by decide +kernel
example : ¬ (windowsep.mag ((gr1 * gr2 + BPair.unit)
      + (gr1p * gr2p + (BPair.ofNat 3).swap).swap)
    ≤ BPair.ofNat 2 * windowsep.mag (gr1 + gr1p.swap)
      + (BPair.ofNat 1 * windowsep.mag (gr2 + gr2p.swap)
        + (BPair.unit + BPair.ofNat 1))) := by decide +kernel

private def wdX : BPair := BPair.ofNat 5
private def wdXX : BPair := BPair.ofNat 3
private def wdY : BPair := BPair.ofNat 2
private def wdYY : BPair := BPair.ofNat 7
private def wdCX : BPair := BPair.ofNat 3
private def wdCY : BPair := BPair.ofNat 2

private theorem wdCapX : windowsep.mag wdXX ≤ wdCX := by decide +kernel
private theorem wdCapY : windowsep.mag wdY ≤ wdCY := by decide +kernel

example : (windowsep.mag (wdX * wdXX + (wdY * wdYY).swap)).oneValue
    (BPair.ofNat 1) := by decide +kernel
example : (wdCX * windowsep.mag (wdX + wdY.swap)
    + wdCY * windowsep.mag (wdXX + wdYY.swap)).oneValue
    (BPair.ofNat 17) := by decide +kernel
example : windowsep.mag (wdX * wdXX + (wdY * wdYY).swap)
    ≤ wdCX * windowsep.mag (wdX + wdY.swap)
      + wdCY * windowsep.mag (wdXX + wdYY.swap) := by decide +kernel
example : windowsep.mag (wdX * wdXX + (wdY * wdYY).swap)
    ≤ wdCX * windowsep.mag (wdX + wdY.swap)
      + wdCY * windowsep.mag (wdXX + wdYY.swap) :=
  prodWidth wdX wdXX wdY wdYY wdCX wdCY wdCapX wdCapY

example : (windowsep.mag (wdX * wdXX + (wdY * wdXX).swap)).oneValue
    (BPair.ofNat 9) := by decide +kernel
example : (wdCX * windowsep.mag (wdX + wdY.swap)
    + wdCY * windowsep.mag (wdXX + wdXX.swap)).oneValue
    (BPair.ofNat 9) := by decide +kernel
example : windowsep.mag (wdX * wdXX + (wdY * wdXX).swap)
    ≤ wdCX * windowsep.mag (wdX + wdY.swap)
      + wdCY * windowsep.mag (wdXX + wdXX.swap) := by decide +kernel
example : windowsep.mag (wdX * wdXX + (wdY * wdXX).swap)
    ≤ wdCX * windowsep.mag (wdX + wdY.swap)
      + wdCY * windowsep.mag (wdXX + wdXX.swap) :=
  prodWidth wdX wdXX wdY wdXX wdCX wdCY wdCapX wdCapY

private def asE : BPair := BPair.ofNat 1
private def asEp : BPair := BPair.ofNat 2
private def asW1 : BPair := BPair.ofNat 3
private def asW2 : BPair := BPair.ofNat 4

private theorem asWid1 : windowsep.mag (wdX + wdY.swap) ≤ asW1 := by
  decide +kernel
private theorem asWid2 : windowsep.mag (wdXX + wdYY.swap) ≤ asW2 := by
  decide +kernel
private theorem asCe : windowsep.mag asE ≤ asE := by decide +kernel
private theorem asCep : windowsep.mag asEp ≤ asEp := by decide +kernel

example : (windowsep.mag ((wdX * wdXX + asE)
    + (wdY * wdYY + asEp).swap)).oneValue BPair.unit := by decide +kernel
example : (wdCX * asW1 + (wdCY * asW2 + (asE + asEp))).oneValue
    (BPair.ofNat 20) := by decide +kernel
example : windowsep.mag ((wdX * wdXX + asE) + (wdY * wdYY + asEp).swap)
    ≤ wdCX * asW1 + (wdCY * asW2 + (asE + asEp)) := by decide +kernel
example : windowsep.mag ((wdX * wdXX + asE) + (wdY * wdYY + asEp).swap)
    ≤ wdCX * asW1 + (wdCY * asW2 + (asE + asEp)) :=
  assemble_close wdX wdXX wdY wdYY asE asEp wdCX wdCY asW1 asW2 asE asEp
    wdCapX wdCapY asWid1 asWid2 asCe asCep

private def dgB : List elim.Mat :=
  [[[(BPair.ofNat 1).swap]], [[(BPair.ofNat 1).swap]]]
private def offB : List elim.Mat := [[[BPair.ofNat 1]]]
private def usB : List greenprod.VecQ :=
  [([BPair.ofNat 1], Pos.one), ([BPair.ofNat 1], Pos.one)]
private def wsB : List greenprod.VecQ :=
  [([BPair.unit], Pos.one), ([BPair.unit], Pos.one)]
private def nsB : List Nat := [1, 1]

private theorem readB : greenprod.solveRead dgB offB usB wsB nsB := by
  decide +kernel
private theorem kerB : greenprod.sidesUnit wsB := by decide +kernel

example : qOneValue (BPair.addQ (rhoBlock wOne dgB usB)
    (BPair.addQ (cBlock wOne offB usB)
      (cBlock (fun k => wOne (k + 1)) offB usB)))
    (BPair.unit, Pos.one) := by decide +kernel
example : qOneValue (BPair.addQ (rhoBlock wOne dgB usB)
    (BPair.addQ (cBlock wOne offB usB)
      (cBlock (fun k => wOne (k + 1)) offB usB)))
    (BPair.unit, Pos.one) :=
  blockFold_sq dgB offB usB wsB nsB readB kerB wOne

example : qOneValue (BPair.addQ (rhoBlock wKey dgB usB)
    (BPair.addQ (cBlock wKey offB usB)
      (cBlock (fun k => wKey (k + 1)) offB usB)))
    (BPair.unit, Pos.one) := by decide +kernel
example : qOneValue (BPair.addQ (rhoBlock wKey dgB usB)
    (BPair.addQ (cBlock wKey offB usB)
      (cBlock (fun k => wKey (k + 1)) offB usB)))
    (BPair.unit, Pos.one) :=
  blockFold_sq dgB offB usB wsB nsB readB kerB wKey

private def dg3 : List elim.Mat :=
  [[[(BPair.ofNat 1).swap]], [[(BPair.ofNat 3).swap]],
    [[(BPair.ofNat 2).swap]]]
private def off3 : List elim.Mat := [[[BPair.ofNat 1]], [[BPair.ofNat 2]]]
private def us3 : List greenprod.VecQ :=
  [([BPair.ofNat 1], Pos.one), ([BPair.ofNat 1], Pos.one),
    ([BPair.ofNat 1], Pos.one)]
private def ws3 : List greenprod.VecQ :=
  [([BPair.unit], Pos.one), ([BPair.unit], Pos.one),
    ([BPair.unit], Pos.one)]
private def ns3 : List Nat := [1, 1, 1]

private theorem read3 : greenprod.solveRead dg3 off3 us3 ws3 ns3 := by
  decide +kernel
private theorem ker3 : greenprod.sidesUnit ws3 := by decide +kernel

example : ((rhoBlock wKey dg3 us3).1).oneValue (BPair.ofNat 7).swap := by
  decide +kernel
example : ((cBlock wKey off3 us3).1).oneValue (BPair.ofNat 2) := by
  decide +kernel
example : ((cBlock (fun k => wKey (k + 1)) off3 us3).1).oneValue
    (BPair.ofNat 5) := by decide +kernel
example : qOneValue (BPair.addQ (rhoBlock wKey dg3 us3)
    (BPair.addQ (cBlock wKey off3 us3)
      (cBlock (fun k => wKey (k + 1)) off3 us3)))
    (BPair.unit, Pos.one) := by decide +kernel
example : qOneValue (BPair.addQ (rhoBlock wKey dg3 us3)
    (BPair.addQ (cBlock wKey off3 us3)
      (cBlock (fun k => wKey (k + 1)) off3 us3)))
    (BPair.unit, Pos.one) :=
  blockFold_sq dg3 off3 us3 ws3 ns3 read3 ker3 wKey

example : (BPair.addQ (rhoBlock wKey dg3 us3)
    (BPair.addQ (cBlock wKey off3 us3)
      (cBlock (fun k => wKey (k + 2)) off3 us3))).1.oneValue
    (BPair.ofNat 3) := by decide +kernel
example : ¬ qOneValue (BPair.addQ (rhoBlock wKey dg3 us3)
    (BPair.addQ (cBlock wKey off3 us3)
      (cBlock (fun k => wKey (k + 2)) off3 us3)))
    (BPair.unit, Pos.one) := by decide +kernel

private def dg2 : List elim.Mat :=
  [[[(BPair.ofNat 1).swap, BPair.unit],
      [BPair.unit, (BPair.ofNat 1).swap]],
    [[(BPair.ofNat 1).swap, BPair.unit],
      [BPair.unit, (BPair.ofNat 1).swap]]]
private def off2 : List elim.Mat :=
  [[[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]]
private def us2 : List greenprod.VecQ :=
  [([BPair.ofNat 1, BPair.ofNat 1], Pos.one),
    ([BPair.ofNat 1, BPair.ofNat 1], Pos.one)]
private def ws2 : List greenprod.VecQ :=
  [([BPair.unit, BPair.unit], Pos.one),
    ([BPair.unit, BPair.unit], Pos.one)]
private def ns2 : List Nat := [2, 2]

private theorem read2 : greenprod.solveRead dg2 off2 us2 ws2 ns2 := by
  decide +kernel
private theorem ker2 : greenprod.sidesUnit ws2 := by decide +kernel

example : qOneValue (BPair.addQ (rhoBlock wKey dg2 us2)
    (BPair.addQ (cBlock wKey off2 us2)
      (cBlock (fun k => wKey (k + 1)) off2 us2)))
    (BPair.unit, Pos.one) := by decide +kernel
example : qOneValue (BPair.addQ (rhoBlock wKey dg2 us2)
    (BPair.addQ (cBlock wKey off2 us2)
      (cBlock (fun k => wKey (k + 1)) off2 us2)))
    (BPair.unit, Pos.one) :=
  blockFold_sq dg2 off2 us2 ws2 ns2 read2 ker2 wKey

private def dgV : List elim.Mat :=
  [[[BPair.unit]], [[(BPair.ofNat 1).swap]]]
private def wsV : List greenprod.VecQ :=
  [([BPair.ofNat 1], Pos.one), ([BPair.unit], Pos.one)]

example : greenprod.solveRead dgV offB usB wsV nsB := by decide +kernel
example : ¬ greenprod.sidesUnit wsV := by decide +kernel
example : ¬ greenprod.solveRead dgB offB usB wsV nsB := by decide +kernel
example : (BPair.addQ (rhoBlock wOne dgV usB)
    (BPair.addQ (cBlock wOne offB usB)
      (cBlock (fun k => wOne (k + 1)) offB usB))).1.oneValue
    (BPair.ofNat 1) := by decide +kernel
example : ¬ qOneValue (BPair.addQ (rhoBlock wOne dgV usB)
    (BPair.addQ (cBlock wOne offB usB)
      (cBlock (fun k => wOne (k + 1)) offB usB)))
    (BPair.unit, Pos.one) := by decide +kernel
