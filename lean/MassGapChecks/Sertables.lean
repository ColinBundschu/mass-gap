import MassGap.Sertables
import MassGap.Inertia
/-!
The check module for `con:sertables`: the batteries re-read the
member tables by kernel `decide`, every read family at all twelve
committed members (`B_{2,3,4}`, `C_{3,4}`, `D_{4,5}`, `G_2`,
`F_4`, `E_6`, `E_7`, `E_8`) — the residue folds with their naming
identities (`r = 2ℓ - 2`, `ℓ`, `2ℓ - 3`, and `3, 8, 11, 17, 29`);
the positive counts (`ℓ²`, `ℓ²`, `ℓ² - ℓ`, and
`6, 24, 36, 63, 120`); the highest root's form read; the form's
simple symmetry; the shape and occupancy reads with the root
fold's coroot reads at the direct-fold members (the series and
`G_2`); and the adjugate rows' coroot witnesses with the θ-fold
rows at the five fold keys.  The `F_4` member closes its
descent-built positive list through the family read — the stored
fold list against the displayed coordinate family, the round trip
with the per-fold key counts and the coroot reads at one forcing,
the occupancy and shape clauses riding the round trip — and the
`E` members close their committed literals twice: the family read
at the literal, and one certifying equation per member reading the
literal as the descent's own output, the `E_8` pair the module's
heavy pins at their own heartbeat allowance, the 120-member
family's descent at the shared Gram.
The defining-table batteries read the triple displays at every
simple key of `B_2`, `C_3` and `D_4` — `B` at its cleared
pairing, `C` and `D` at the identity weight — with two committed
refusals at the `B` short move (the forged raising reading the
doubled entry at one, and the plain identity in place of the
cleared pairing) and the invariant counts at the dual pair's
line.  Budget: the pair-partition counts sit beyond the kernel
allowance — `invCountB 2 2` at 190 s user by kernel decide,
`invCountC 3 2` refusing the 4000000-heartbeat allowance at
318 s user, `invCountD 4 2` beyond both — each value `3` at the
compiled evaluator, the stacked matrix's elimination the whole
cost.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground gentable sertables

/-! The `B_2` member data the member-tier batteries state — the
table, the vacant content, the one-hot top, the `ρ`-orbit with its
dominance witnesses, the `ω_1`-block's multiplicity family, and the
`λ+ρ`-orbit — one stated copy at `con:sertables`' first series
member, the member-tier check modules' shared data. -/

namespace sertables

def tB2 : gentable.Table := tableB 2

def zeroV : List BPair := List.replicate 2 BPair.unit

def lamB2 : List BPair := [BPair.ofNat 1, BPair.unit]

def wB2 : List (List BPair × Bool) :=
  [([(BPair.ofNat 1), (BPair.ofNat 1)], false),
   ([(BPair.ofNat 1).swap, (BPair.ofNat 3)], true),
   ([(BPair.ofNat 2), (BPair.ofNat 1).swap], true),
   ([(BPair.ofNat 2).swap, (BPair.ofNat 3)], false),
   ([(BPair.ofNat 1), (BPair.ofNat 3).swap], true),
   ([(BPair.ofNat 1).swap, (BPair.ofNat 1).swap], false),
   ([(BPair.ofNat 2).swap, (BPair.ofNat 1)], true),
   ([(BPair.ofNat 2), (BPair.ofNat 3).swap], false)]

def witsB2 : List (List Nat) :=
  [[0, 0], [1, 0], [0, 1], [2, 1], [2, 4], [3, 4], [3, 3], [1, 3]]

def mB2 : List (List BPair) :=
  [[BPair.ofNat 1, BPair.unit],
   [(BPair.ofNat 1).swap, BPair.ofNat 2],
   [BPair.unit, BPair.unit],
   [BPair.ofNat 1, (BPair.ofNat 2).swap],
   [(BPair.ofNat 1).swap, BPair.unit]]

def mwitsB2 : List (List Nat) :=
  [[0, 0], [1, 0], [1, 1], [1, 2], [2, 2]]

def wpB2 : List (List BPair × Bool) :=
  [([(BPair.ofNat 2), (BPair.ofNat 1)], false),
   ([(BPair.ofNat 2).swap, (BPair.ofNat 5)], true),
   ([(BPair.ofNat 3), (BPair.ofNat 1).swap], true),
   ([(BPair.ofNat 3), (BPair.ofNat 5).swap], false),
   ([(BPair.ofNat 3).swap, (BPair.ofNat 5)], false),
   ([(BPair.ofNat 3).swap, (BPair.ofNat 1)], true),
   ([(BPair.ofNat 2), (BPair.ofNat 5).swap], true),
   ([(BPair.ofNat 2).swap, (BPair.ofNat 1).swap], false)]

def wpwitsB2 : List (List Nat) :=
  [[0, 0], [2, 0], [0, 1], [2, 5], [3, 1], [5, 5], [3, 6], [5, 6]]

end sertables

/-! The residue folds per member, each with its naming identity. -/

example : residue (tableB 2) = 2 := by decide +kernel
example : residue (tableB 3) = 4 := by decide +kernel
example : residue (tableB 4) = 6 := by decide +kernel
example : residue (tableC 3) = 3 := by decide +kernel
example : residue (tableC 4) = 4 := by decide +kernel
example : residue (tableD 4) = 5 := by decide +kernel
example : residue (tableD 5) = 7 := by decide +kernel
example : residue tableG2 = 3 := by decide +kernel
example : residue tableF4 = 8 := by decide +kernel
example : residue tableE6 = 11 := by decide +kernel
example : residue tableE7 = 17 := by decide +kernel
example : residue tableE8 = 29 := by decide +kernel

example : residueRead (tableB 2) := by decide +kernel
example : residueRead (tableB 3) := by decide +kernel
example : residueRead (tableB 4) := by decide +kernel
example : residueRead (tableC 3) := by decide +kernel
example : residueRead (tableC 4) := by decide +kernel
example : residueRead (tableD 4) := by decide +kernel
example : residueRead (tableD 5) := by decide +kernel
example : residueRead tableG2 := by decide +kernel
example : residueRead tableF4 := by decide +kernel
example : residueRead tableE6 := by decide +kernel
example : residueRead tableE7 := by decide +kernel
example : residueRead tableE8 := by decide +kernel

/-! The positive counts: `ℓ²` at `B` and `C`, `ℓ² - ℓ` at `D`,
and the fixed members' displayed counts. -/

example : posCount (tableB 2) = 4 := by decide +kernel
example : posCount (tableB 3) = 9 := by decide +kernel
example : posCount (tableB 4) = 16 := by decide +kernel
example : posCount (tableC 3) = 9 := by decide +kernel
example : posCount (tableC 4) = 16 := by decide +kernel
example : posCount (tableD 4) = 12 := by decide +kernel
example : posCount (tableD 5) = 20 := by decide +kernel
example : posCount tableG2 = 6 := by decide +kernel
example : posCount tableF4 = 24 := by decide +kernel
example : posCount tableE6 = 36 := by decide +kernel
example : posCount tableE7 = 63 := by decide +kernel
example : posCount tableE8 = 120 := by decide +kernel

/-! The highest root's form read per member. -/

example : thetaNormRead (tableB 2) := by decide +kernel
example : thetaNormRead (tableB 3) := by decide +kernel
example : thetaNormRead (tableB 4) := by decide +kernel
example : thetaNormRead (tableC 3) := by decide +kernel
example : thetaNormRead (tableC 4) := by decide +kernel
example : thetaNormRead (tableD 4) := by decide +kernel
example : thetaNormRead (tableD 5) := by decide +kernel
example : thetaNormRead tableG2 := by decide +kernel
example : thetaNormRead tableF4 := by decide +kernel
example : thetaNormRead tableE6 := by decide +kernel
example : thetaNormRead tableE7 := by decide +kernel
example : thetaNormRead tableE8 := by decide +kernel

/-! The form's simple symmetry per member. -/

example : symRead (tableB 2) := by decide +kernel
example : symRead (tableB 3) := by decide +kernel
example : symRead (tableB 4) := by decide +kernel
example : symRead (tableC 3) := by decide +kernel
example : symRead (tableC 4) := by decide +kernel
example : symRead (tableD 4) := by decide +kernel
example : symRead (tableD 5) := by decide +kernel
example : symRead tableG2 := by decide +kernel
example : symRead tableF4 := by decide +kernel
example : symRead tableE6 := by decide +kernel
example : symRead tableE7 := by decide +kernel
example : symRead tableE8 := by decide +kernel

/-! The shape, occupancy and root-fold coroot reads at the
direct-fold members, the series and `G_2` (the descent-built
members' positive lists close through the family reads below,
the three clauses riding the round trip there). -/

example : shapeRead (tableB 2) := by decide +kernel
example : shapeRead (tableB 3) := by decide +kernel
example : shapeRead (tableB 4) := by decide +kernel
example : shapeRead (tableC 3) := by decide +kernel
example : shapeRead (tableC 4) := by decide +kernel
example : shapeRead (tableD 4) := by decide +kernel
example : shapeRead (tableD 5) := by decide +kernel
example : shapeRead tableG2 := by decide +kernel

example : occRead (tableB 2) := by decide +kernel
example : occRead (tableB 3) := by decide +kernel
example : occRead (tableB 4) := by decide +kernel
example : occRead (tableC 3) := by decide +kernel
example : occRead (tableC 4) := by decide +kernel
example : occRead (tableD 4) := by decide +kernel
example : occRead (tableD 5) := by decide +kernel
example : occRead tableG2 := by decide +kernel

example : rhoRead (tableB 2) := by decide +kernel
example : rhoRead (tableB 3) := by decide +kernel
example : rhoRead (tableB 4) := by decide +kernel
example : rhoRead (tableC 3) := by decide +kernel
example : rhoRead (tableC 4) := by decide +kernel
example : rhoRead (tableD 4) := by decide +kernel
example : rhoRead (tableD 5) := by decide +kernel
example : rhoRead tableG2 := by decide +kernel

/-! The family reads at the descent-built members: the table's own
positive list against the displayed coordinate family, the round
trip with the per-fold key counts and the coroot reads at one
forcing.  The `E_8` read is the module's heavy pin, the 120-member family
at the shared Gram. -/

example : famRead tableF4 f4Simples f4Family := by decide +kernel

set_option maxHeartbeats 16000000 in
example : famRead tableE6 (e8Simples.take 6) (e8Family.filter selE6) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
example : famRead tableE7 (e8Simples.take 7) (e8Family.filter selE7) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
example : famRead tableE8 e8Simples e8Family := by decide +kernel

/-! The committed positive-list literals are the descent's own
outputs: one certifying equation per `E`-member against
`descentAll`, so every further read walks the literal. -/

set_option maxHeartbeats 16000000 in
example : descentAll (e8Simples.take 6) 64 (e8Family.filter selE6)
    = posE6 := by decide +kernel

set_option maxHeartbeats 16000000 in
example : descentAll (e8Simples.take 7) 64 (e8Family.filter selE7)
    = posE7 := by decide +kernel

set_option maxHeartbeats 16000000 in
example : descentAll e8Simples 64 e8Family = posE8 := by
  decide +kernel

/-! The adjugate rows: the coroot witnesses at the five fold keys
`1, 1, 3, 2, 1`, and the θ-fold rows. -/

example : adjRead tableG2 1 adjG2 := by decide +kernel
example : adjRead tableF4 1 adjF4 := by decide +kernel
example : adjRead tableE6 3 adjE6 := by decide +kernel
example : adjRead tableE7 2 adjE7 := by decide +kernel
example : adjRead tableE8 1 adjE8 := by decide +kernel

example : thetaRowRead tableG2 1 adjG2 1 := by decide +kernel
example : thetaRowRead tableF4 1 adjF4 0 := by decide +kernel
example : thetaRowRead tableE6 3 adjE6 1 := by decide +kernel
example : thetaRowRead tableE7 2 adjE7 0 := by decide +kernel
example : thetaRowRead tableE8 1 adjE8 7 := by decide +kernel

/-! The defining tables: the triple reads at every simple key of
`B_2`, `C_3` and `D_4`, `B` at its cleared pairing and `C` and `D`
at the identity weight. -/

example : tripleRead (wB 2) (raiseB 2 0) (lowerB 2 0) (hDiagB 2 0) := by
  decide +kernel
example : tripleRead (wB 2) (raiseB 2 1) (lowerB 2 1) (hDiagB 2 1) := by
  decide +kernel

example : tripleRead (inertia.idMat (vcountC 3)) (raiseC 3 0)
    (lowerC 3 0) (hDiagC 3 0) := by decide +kernel
example : tripleRead (inertia.idMat (vcountC 3)) (raiseC 3 1)
    (lowerC 3 1) (hDiagC 3 1) := by decide +kernel
example : tripleRead (inertia.idMat (vcountC 3)) (raiseC 3 2)
    (lowerC 3 2) (hDiagC 3 2) := by decide +kernel

example : tripleRead (inertia.idMat (vcountD 4)) (raiseD 4 0)
    (lowerD 4 0) (hDiagD 4 0) := by decide +kernel
example : tripleRead (inertia.idMat (vcountD 4)) (raiseD 4 1)
    (lowerD 4 1) (hDiagD 4 1) := by decide +kernel
example : tripleRead (inertia.idMat (vcountD 4)) (raiseD 4 2)
    (lowerD 4 2) (hDiagD 4 2) := by decide +kernel
example : tripleRead (inertia.idMat (vcountD 4)) (raiseD 4 3)
    (lowerD 4 3) (hDiagD 4 3) := by decide +kernel

/-! The committed refusals at the `B` short move: the forged
raising with the doubled entry read at one, and the plain identity
in place of the cleared pairing. -/

private def forgedShortB : elim.Mat :=
  ground.matOf 5 5 (fun r c =>
    if r == 1 && c == 4 then BPair.ofNat 1
    else if r == 4 && c == 3 then BPair.ofNat 1
    else BPair.unit)

example : ¬ tripleRead (wB 2) forgedShortB (lowerB 2 1)
    (hDiagB 2 1) := by decide +kernel

example : ¬ tripleRead (inertia.idMat (vcountB 2)) (raiseB 2 1)
    (lowerB 2 1) (hDiagB 2 1) := by decide +kernel

/-! The invariant counts at the dual pair's line, one per
series. -/

example : invCountB 2 1 = 1 := by decide +kernel
example : invCountC 3 1 = 1 := by decide +kernel
example : invCountD 4 1 = 1 := by decide +kernel

/-! The coordinate tier at `B_2` and `G_2`: the fundamental data at
the coroot presentation — the cleared Gram with its scale, the
simple members' positions in the positive list, and the
reflections' permutations of it — read at the ten clauses, the
shape conjuncts, the Gram's defining read against the Cartan rows
with its symmetry and an inertia split certificate, the simple
positions, the involution and form-keeping reads, the permutation
of the positive list, and the `ρ`-dot positivity. -/


private def spGramB2 : inertia.Split 2 :=
  ⟨⟨[[BPair.ofNat 1, (BPair.ofNat 1).swap],
     [BPair.ofNat 0, BPair.ofNat 2]], rfl⟩,
   ⟨[[BPair.ofNat 2, BPair.ofNat 1],
     [BPair.ofNat 0, BPair.ofNat 1]], rfl⟩,
   [.one (BPair.ofNat 2), .one (BPair.ofNat 2)], 0, rfl⟩

private def spGramG2 : inertia.Split 2 :=
  ⟨⟨[[BPair.ofNat 1, (BPair.ofNat 6).swap],
     [BPair.ofNat 0, BPair.ofNat 4]], rfl⟩,
   ⟨[[BPair.ofNat 4, BPair.ofNat 6],
     [BPair.ofNat 0, BPair.ofNat 1]], rfl⟩,
   [.one (BPair.ofNat 4), .one (BPair.ofNat 48)], 0, rfl⟩

example : fundShape tB2 fundB2 := by decide +kernel
example : gramRead tB2 fundB2 := by decide +kernel
example : gramSymRead fundB2 := by decide +kernel
example : inertia.splitRead fundB2.gram spGramB2 := by decide +kernel
example : inertia.pdAt spGramB2 := by decide +kernel
example : simplePosRead tB2 fundB2 := by decide +kernel
example : reflSquareRead tB2 := by decide +kernel
example : permSquareRead tB2 fundB2 := by decide +kernel
example : reflFormRead tB2 fundB2 := by decide +kernel
example : permImageRead tB2 fundB2 := by decide +kernel
example : rhoDotRead tB2 fundB2 := by decide +kernel

/-! The Gram-side reads' classification at `balanceRead`: the
theorem's conclusion binds no field of the fundamental data, so no
fundamental-data forgery can refuse it — the defining read, the
symmetry and the shape sit in the frame class at the conclusion's
own shape, each pinned at the stated members and refused at the
committed forged tables' own batteries.  `gentable.rhoRead` binds
nowhere at all: it is four of its co-binders' own consequence,
landed as `assembly.rhoRead_derived` — `con:sertables`' own
sentence `s_i(2ρ) + 2α_i = 2ρ`, so the root fold's coroot pairs
read `(2ρ)(α_i^∨) = 2` — and withdrawn from `balanceRead`'s
signature.  The derivation: at the stated family's vector sum `T`
a letter reads `s_i T` two ways, the reflection join's kick at
`T`'s own coroot pair at `i` and the image clauses memberwise
(the simple's position crossing to its balance partner, every
further key carried along the permutation), and the permuted
remainder the two readings share cancels, placing the member at
the permutation's image `q` of the simple's position at
`(T_i - 1) α_i`.  Where `q` is the simple's own position the
cancelled positive `ρ`-dot reads `T_i` at two; off it the
permutation datum's involution returns at `q` — it carries `q`
back to the simple's position, so that member's own image clause
reads `α_i` itself — and the returned reading is what forces the
multiple negative, the member's `ρ`-dot joining the simple's to
the sum's unit against two strictly positive dots.  So `T_i`
reads two at every key, and no isolating forgery exists. -/

example : fundShape tableG2 fundG2 := by decide +kernel
example : gramRead tableG2 fundG2 := by decide +kernel
example : gramSymRead fundG2 := by decide +kernel
example : inertia.splitRead fundG2.gram spGramG2 := by decide +kernel
example : inertia.pdAt spGramG2 := by decide +kernel
example : simplePosRead tableG2 fundG2 := by decide +kernel
example : reflSquareRead tableG2 := by decide +kernel
example : permSquareRead tableG2 fundG2 := by decide +kernel
example : reflFormRead tableG2 fundG2 := by decide +kernel
example : permImageRead tableG2 fundG2 := by decide +kernel
example : rhoDotRead tableG2 fundG2 := by decide +kernel

/-! The committed refusals at the coordinate tier, each forged
datum's refusing reads pinned with the reads it leaves untouched
beside them. -/

-- the Gram forged symmetric off the Cartan rows' scaled diagonal:
-- the defining read refuses, the ρ-dot read with it (the Gram
-- enters the pairing), the symmetry alone deciding nothing
private def forgedGramB2 : FundData :=
  ⟨[[(BPair.ofNat 2), (BPair.ofNat 1)],
    [(BPair.ofNat 1), (BPair.ofNat 2)]],
   fundB2.scale, fundB2.simplePos, fundB2.perms⟩

example : ¬ gramRead tB2 forgedGramB2 := by decide +kernel
example : ¬ rhoDotRead tB2 forgedGramB2 := by decide +kernel
example : gramSymRead forgedGramB2 := by decide +kernel

-- the second simple's position forged off the positive list's
-- one-key fold: the simple positions' read refuses, the image
-- read with it (the images read at the simple's coroot vector),
-- the shape and square reads untouched
private def forgedSimplePosB2 : FundData :=
  ⟨fundB2.gram, fundB2.scale, [0, 2], fundB2.perms⟩

example : ¬ simplePosRead tB2 forgedSimplePosB2 := by decide +kernel
example : ¬ permImageRead tB2 forgedSimplePosB2 := by decide +kernel
example : fundShape tB2 forgedSimplePosB2 := by decide +kernel
example : permSquareRead tB2 forgedSimplePosB2 := by decide +kernel

-- the permutations forged to the identity and the leading
-- transposition: both stay involutions, so the involution read
-- passes and the permutation read refuses at the images
private def forgedPermsB2 : FundData :=
  ⟨fundB2.gram, fundB2.scale, fundB2.simplePos,
   [[0, 1, 2, 3], [1, 0, 2, 3]]⟩

example : ¬ permImageRead tB2 forgedPermsB2 := by decide +kernel
example : permSquareRead tB2 forgedPermsB2 := by decide +kernel
