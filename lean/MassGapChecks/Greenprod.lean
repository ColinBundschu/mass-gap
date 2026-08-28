import MassGap.Greenprod
/-!
The check module for `lem:greenprod`: the batteries re-read the
slab arithmetic by kernel `decide` at three instances.  The scalar
three-slab chain `tridiag(3,3,3; 1,1)` — the two recursions at the
cleared witnesses (`X = (21/8, 8/3, 3)`, `Y` its reflection), the
Green solve at the middle source (`Z₂ = 7/3`,
`u = (-1/7, 3/7, -1/7)`), the transfer telescopes on both sides,
the descending telescope's occupancy arm at vacant sides — a source
key past the slabs refuses with every step below it standing — and
the transfer join's unit read.  The signed two-slab
`tridiag(1,-1; 1)` — the count split's coherence, `rev(S) = 1` at
the assembled matrix against the slab fold over the pivots
`(2, -1)`, with the refusal pins at a forged witness, at off-order
slab shapes and at an exchanged certificate pair, and the coherence
bundle read a second time through `countSplit_read`.  The two-by-two
block slab `tridiag(2I, 3I; I)` — the rectangular shape read and the
determinant split `det S = 25 = (25/9)(9)` at the cleared minors.
The three-slab chain rides its count split too: the three pivots'
certificates at the identity congruence against the assembled
datum's own at the cleared descent, `rev(S) = 0` through
`countSplit` and by the kernel, with the bundle whole through
`countSplit_read`.  The vacant-slab forgery closes the module — one
occupied scalar slab beside a slab of order `0`, the occupancy
conjunct the isolating binder, every co-binder of the bundle decided
beside it and the two counts parting at `0` against `1`.  The
decimated head reads last — clause (i)'s head onto the depths at or
below `j` at a two-slab instance cleared at its pivot: the head's
own entries, its square order at the leading key joined to the
depth's, and the two cross-scaled heads' tie display decided at an
occupied drift and at equal members, refused at a diagonal off the
tie, refused with the coupling read at a second window's coupling
off the shared occupied one, and landed whole through `headM_tie`
at the occupied drift and at the vacant depth. -/
set_option maxHeartbeats 4000000

open ground elim inertia greenprod

private def u : BPair := BPair.unit

/-! The scalar three-slab chain `tridiag(3,3,3; 1,1)`. -/

private def diag3 : List Mat := [[[⟨4, 1⟩]], [[⟨4, 1⟩]], [[⟨4, 1⟩]]]
private def off3 : List Mat := [[[⟨2, 1⟩]], [[⟨2, 1⟩]]]
private def xs3 : List MatQ :=
  [⟨[[⟨22, 1⟩]], 8⟩, ⟨[[⟨9, 1⟩]], 3⟩, ⟨[[⟨4, 1⟩]], 1⟩]
private def rs3 : List MatQ := [⟨[[⟨4, 1⟩]], 8⟩, ⟨[[⟨2, 1⟩]], 3⟩]
private def ys3 : List MatQ :=
  [⟨[[⟨4, 1⟩]], 1⟩, ⟨[[⟨9, 1⟩]], 3⟩, ⟨[[⟨22, 1⟩]], 8⟩]
private def cs3 : List MatQ := [⟨[[⟨2, 1⟩]], 3⟩, ⟨[[⟨4, 1⟩]], 8⟩]
private def us3 : List VecQ :=
  [⟨[⟨1, 2⟩], 7⟩, ⟨[⟨4, 1⟩], 7⟩, ⟨[⟨1, 2⟩], 7⟩]
private def ws3 : List VecQ := [⟨[u], 1⟩, ⟨[⟨2, 1⟩], 1⟩, ⟨[u], 1⟩]

example : slabShape diag3 off3 [1, 1, 1] := by decide +kernel
example : tailRead diag3 off3 xs3 rs3 [1, 1, 1] := by decide +kernel
example : headRead diag3 off3 ys3 cs3 [1, 1, 1] := by decide +kernel
example : greenRead diag3 off3 xs3 rs3 ys3 cs3 us3 ws3 1 [1, 1, 1] := by
  decide +kernel

/-! The descending telescope's occupancy arm at vacant sides: every
step below the source reads, and a source key past the slabs
refuses. -/

private def usZ : List VecQ := [⟨[u], 1⟩, ⟨[u], 1⟩, ⟨[u], 1⟩]

example : teleDown cs3 usZ 2 [1, 1, 1] := by decide +kernel
-- the walk's own occupancy arm, the shape reads and every step below
-- the key standing beside it
example : ¬ teleDown cs3 usZ 3 [1, 1, 1] := by decide +kernel

/-! The ascending telescope's occupancy arm: the source at the last
slab reads vacuously, and a source key past the slabs refuses at
the walk's own descent with both shape reads standing. -/

example : teleUp rs3 us3 2 [1, 1, 1] := by decide +kernel
example : ¬ teleUp rs3 us3 3 [1, 1, 1] := by decide +kernel

/-! The source support's key: the occupied middle slab passes at
its own key alone, either further key leaving it unskipped. -/

example : supportAt ws3 1 := by decide +kernel
example : ¬ supportAt ws3 0 := by decide +kernel
example : ¬ supportAt ws3 2 := by decide +kernel

/-! The head recursion's isolating refusals: the seed at a forged
leading diagonal with every step read standing, and the first
witness solve at a forged head witness with the seed and the shape
reads standing. -/

private def diagF : List Mat := [[[⟨5, 1⟩]], [[⟨4, 1⟩]], [[⟨4, 1⟩]]]
private def csF : List MatQ := [⟨[[⟨3, 1⟩]], 3⟩, ⟨[[⟨4, 1⟩]], 8⟩]

example : ¬ headRead diagF off3 ys3 cs3 [1, 1, 1] := by decide +kernel
example : ¬ headRead diag3 off3 ys3 csF [1, 1, 1] := by decide +kernel

/-! The row walk's isolating refusal: one forged solution block
parts the middle row with the shape reads standing. -/

private def usF : List VecQ :=
  [⟨[⟨1, 2⟩], 7⟩, ⟨[⟨5, 1⟩], 7⟩, ⟨[⟨1, 2⟩], 7⟩]

example : ¬ solveRead diag3 off3 usF ws3 [1, 1, 1] := by decide +kernel

/-! The two remaining shape walks' standalone refusals, each at the
member read with the count standing. -/

example : ¬ wShapeC [⟨[[⟨2, 1⟩, ⟨9, 1⟩]], 3⟩, ⟨[[⟨4, 1⟩]], 8⟩]
    [1, 1, 1] := by decide +kernel
example : ¬ vShape [⟨[u, u], 1⟩] [1] := by decide +kernel

/-! The transfer join's unit read at the first head witness,
`Y₁ T₁ + B₁` the sum's unit. -/

example : matNull
    (addQ (mulQ ([[⟨4, 1⟩]], 1) (transfer ([[⟨2, 1⟩]], 3)))
      (ofM [[⟨2, 1⟩]])).1 := by decide +kernel

/-! The forged witness refuses: the tail recursion at `R₂ = 1`
against the solved `1/3`. -/

example : ¬ tailRead diag3 off3 xs3
    [⟨[[⟨4, 1⟩]], 8⟩, ⟨[[⟨2, 1⟩]], 1⟩] [1, 1, 1] := by decide +kernel

/-! The signed two-slab `tridiag(1,-1; 1)`: the count split's
coherence at the assembled matrix, `rev(S) = 1 = 0 + 1` over the
pivots `(2, -1)`. -/

private def diag2 : List Mat := [[[⟨2, 1⟩]], [[⟨1, 2⟩]]]
private def off2 : List Mat := [[[⟨2, 1⟩]]]
private def xs2 : List MatQ := [⟨[[⟨3, 1⟩]], 1⟩, ⟨[[⟨1, 2⟩]], 1⟩]
private def rs2 : List MatQ := [⟨[[⟨1, 2⟩]], 1⟩]
private def s2 : Mat := [[⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 2⟩]]
private def sps2 : List ((n : Nat) × Split n) :=
  [⟨1, ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one ⟨3, 1⟩], 0, rfl⟩⟩,
   ⟨1, ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one ⟨1, 2⟩], 0, rfl⟩⟩]
private def sp2 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 2⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨2, 1⟩, .one ⟨1, 3⟩], 0, rfl⟩

example : matOneValue s2 (assemble diag2 off2) := by decide +kernel
example : tailRead diag2 off2 xs2 rs2 [1, 1] := by decide +kernel
example : revListRead xs2 sps2 := by decide +kernel
example : revFold sps2 = 1 := by decide +kernel
example : countSplitRead s2 diag2 off2 xs2 rs2 sps2 sp2 [1, 1] := by
  decide +kernel
example : detProdRead diag2 off2 xs2 [1, 1] := by decide +kernel

/-! The coherence bundle through the theorem at the signed pair, the
four hypothesis reads decided at the committed data. -/

example : countSplitRead s2 diag2 off2 xs2 rs2 sps2 sp2 [1, 1] :=
  countSplit_read s2 diag2 off2 xs2 rs2 [1, 1] sps2 sp2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The off-order shapes refuse: a short order list, and a ragged
off-diagonal block. -/

example : ¬ slabShape diag2 off2 [1] := by decide +kernel
example : ¬ slabShape diag2 [[[⟨2, 1⟩, ⟨2, 1⟩]]] [1, 1] := by decide +kernel

/-! The certificate list's own read refuses at an exchanged pair:
the two slabs' certificates traded, each pivot against the other
slab's block. -/

private def sps2Ex : List ((n : Nat) × Split n) :=
  [⟨1, ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one ⟨1, 2⟩], 0, rfl⟩⟩,
   ⟨1, ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one ⟨3, 1⟩], 0, rfl⟩⟩]

example : ¬ revListRead xs2 sps2Ex := by decide +kernel

/-! The two-by-two block slab `tridiag(2I, 3I; I)`: the rectangular
shape read, the tail recursion at block witnesses, and the
determinant split `det S = 25 = (25/9)(9)` at the cleared
minors. -/

private def a1 : Mat := [[⟨3, 1⟩, u], [u, ⟨3, 1⟩]]
private def a2 : Mat := [[⟨4, 1⟩, u], [u, ⟨4, 1⟩]]
private def b1 : Mat := [[⟨2, 1⟩, u], [u, ⟨2, 1⟩]]
private def xsB : List MatQ :=
  [⟨[[⟨6, 1⟩, u], [u, ⟨6, 1⟩]], 3⟩, ⟨a2, 1⟩]
private def rsB : List MatQ := [⟨b1, 3⟩]

example : slabShape [a1, a2] [b1] [2, 2] := by decide +kernel
example : ¬ tailRead [a1, a2] [b1] xsB
    [⟨[[⟨2, 1⟩], [u, ⟨2, 1⟩]], 3⟩] [2, 2] := by decide +kernel
example : tailRead [a1, a2] [b1] xsB rsB [2, 2] := by decide +kernel
example : detProdRead [a1, a2] [b1] xsB [2, 2] := by decide +kernel

/-! The count split at the scalar three-slab chain: the three pivots
are positive at order one, so each certificate sits at the identity
congruence, and the assembled `tridiag(3,3,3; 1,1)` splits at the
cleared descent's congruence — the columns `e₁`, `(-1,3,0)`,
`(1,-3,8)` at the leading minors `3, 8, 21`, the block diagonal
`diag(3, 24, 168)` their consecutive products.  Both sides read the
upper side throughout, the count identity through the theorem and by
the kernel beside it. -/

private def sps3 : List ((n : Nat) × Split n) :=
  [⟨1, ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one ⟨22, 1⟩], 0, rfl⟩⟩,
   ⟨1, ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one ⟨9, 1⟩], 0, rfl⟩⟩,
   ⟨1, ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one ⟨4, 1⟩], 0, rfl⟩⟩]

private def s3 : Mat :=
  [[⟨4, 1⟩, ⟨2, 1⟩, u], [⟨2, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩, ⟨4, 1⟩]]

private def sp3 : Split 3 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩], [u, ⟨4, 1⟩, ⟨1, 4⟩], [u, u, ⟨9, 1⟩]], rfl⟩,
   ⟨[[⟨25, 1⟩, ⟨9, 1⟩, u], [u, ⟨9, 1⟩, ⟨4, 1⟩], [u, u, ⟨4, 1⟩]], rfl⟩,
   [.one ⟨4, 1⟩, .one ⟨25, 1⟩, .one ⟨169, 1⟩], 0, rfl⟩

example : matOneValue s3 (assemble diag3 off3) := by decide +kernel
example : revListRead xs3 sps3 := by decide +kernel
example : splitRead s3 sp3 := by decide +kernel
example : revFold sps3 = 0 := by decide +kernel
example : revAt sp3 = 0 := by decide +kernel

example : revAt sp3 = revFold sps3 :=
  countSplit diag3 off3 xs3 rs3 [1, 1, 1] sps3 sp3
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : revAt sp3 = revFold sps3 := by decide +kernel

example : countSplitRead s3 diag3 off3 xs3 rs3 sps3 sp3 [1, 1, 1] :=
  countSplit_read s3 diag3 off3 xs3 rs3 [1, 1, 1] sps3 sp3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The count split's refusal at a vacant slab, the occupancy
conjunct the isolating binder.  The forged data is one occupied
scalar slab beside a slab of order `0`: the shape read refuses at
the order list, and the tail recursion with it, while every other
conjunct of the coherence bundle passes — the assembly reads `[0]`,
the certificate list reads the pivots, the assembled datum splits at
the kernel block, and the two counts part at `0` against `1`. -/

private def dgV : List Mat := [[[u]], []]
private def ogV : List Mat := [[[]]]
private def nsV : List Nat := [1, 0]
private def xsV : List MatQ := [⟨[[⟨1, 2⟩]], 1⟩, ⟨[], 1⟩]
private def rsV : List MatQ := [⟨[], 1⟩]
private def sV : Mat := [[u]]
private def spV : Split 1 := ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [], 1, rfl⟩
private def spsV : List ((n : Nat) × Split n) :=
  [⟨1, ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one ⟨1, 2⟩], 0, rfl⟩⟩,
   ⟨0, ⟨⟨[], rfl⟩, ⟨[], rfl⟩, [], 0, rfl⟩⟩]

example : ¬ slabShape dgV ogV nsV := by decide +kernel
example : ¬ tailRead dgV ogV xsV rsV nsV := by decide +kernel

example : assemble dgV ogV = sV := by decide +kernel
example : revListRead xsV spsV := by decide +kernel
example : splitRead sV spV := by decide +kernel
example : revAt spV = 0 ∧ revFold spsV = 1 := by decide +kernel

/-! The count split's further binder records.  The certificate read
`hl` at the conclusion: a split list of the wrong reversal fold —
the vacant-count certificate at the first pivot's carrier — refuses
the read and parts the conclusion beside it, `0` against `1`.  The
whole-datum split `hS` at the conclusion: the all-kernel split of a
further matrix refuses the assembled read with the fold standing,
the counts parting.  The recursion's list arms refuse at either
mismatch. -/

private def sps2W : List ((n : Nat) × Split n) :=
  [⟨1, ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [], 1, rfl⟩⟩,
   ⟨1, ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one ⟨3, 1⟩], 0, rfl⟩⟩]

example : ¬ revListRead xs2 sps2W := by decide +kernel
example : ¬ (revAt sp2 = revFold sps2W) := by decide +kernel

private def spK2 : Split 2 := ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [], 2, rfl⟩

example : ¬ splitRead (assemble diag2 off2) spK2 := by decide +kernel
example : ¬ (revAt spK2 = revFold sps2) := by decide +kernel

example : ¬ revListRead xs2 [⟨1, ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩,
    [.one ⟨3, 1⟩], 0, rfl⟩⟩] := by decide +kernel
example : ¬ revListRead ([] : List MatQ) sps2 := by decide +kernel

/-! The decimated head at the two-slab instance `tridiag(4,2;0)`
cleared at the pivot `(5/2)`: the head's own entries, its square
order at the leading key joined to the depth's, and clause (i)'s
tie display decided at two drifts and refused off the tie, the
shared certificates named once and consumed by term. -/

private def diagH : List Mat := [[[⟨5, 1⟩]], [[⟨3, 1⟩]]]
private def offH : List Mat := [[[⟨1, 1⟩]]]
private def nsH : List Nat := [1, 1]
private def XH : MatQ := ⟨[[⟨7, 2⟩]], 2⟩

private theorem shpH : slabShape diagH offH nsH := by decide +kernel

private theorem hjH : 1 < nsH.length := by decide +kernel

private theorem sqXH : sqAt XH.1 (ground.getAt 0 nsH 1) := by
  decide +kernel

example : matOneValue (headM diagH offH XH 1)
    [[⟨10, 2⟩, ⟨2, 2⟩], [⟨2, 2⟩, ⟨7, 2⟩]] := by decide +kernel

example : sqAt (headM diagH offH XH 1)
    (ground.sumNat (List.take 1 nsH) + ground.getAt 0 nsH 1) :=
  headM_sq diagH offH XH 1 nsH shpH hjH sqXH

/-! The tie's display at an occupied drift `dn = 1`: the primed
window's depth-0 diagonal raised by the drift at the shared
coupling, the second pivot `(8/1)`, and the two cleared heads
cross-scaled parting at the drift's leading diagonal and at the
cleared pivot difference. -/

private def dnT : BPair := ⟨2, 1⟩
private def diagT : List Mat := [[[⟨6, 1⟩]], [[⟨3, 1⟩]]]
private def XT : MatQ := ⟨[[⟨9, 1⟩]], 1⟩

private theorem shpT : slabShape diagT offH nsH := by decide +kernel

private theorem sqXT : sqAt XT.1 (ground.getAt 0 nsH 1) := by
  decide +kernel

private theorem hdagT : ∀ i, i < 1 →
    matOneValue (ground.getAt [] diagT i)
      (matAdd (ground.getAt [] diagH i)
        (matScaleB dnT (idMat (ground.getAt 0 nsH i))))
  | 0, _ => by decide +kernel
  | _ + 1, h => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)

private theorem hoffT : ∀ i, i < 1 →
    matOneValue (ground.getAt [] offH i) (ground.getAt [] offH i)
  | 0, _ => by decide +kernel
  | _ + 1, h => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)

example : matOneValue (matScale XH.2 (headM diagT offH XT 1))
    (matAdd (matScale XT.2 (headM diagH offH XH 1))
      (matAdd
        (matScaleB (dnT.scale (XH.2 * XT.2))
          (inertia.headId (ground.sumNat (List.take 1 nsH))
            (ground.getAt 0 nsH 1)))
        (inertia.trailPad (ground.sumNat (List.take 1 nsH))
          (addQ XT (swapQ XH)).1))) := by decide +kernel

example : matOneValue (matScale XH.2 (headM diagT offH XT 1))
    (matAdd (matScale XT.2 (headM diagH offH XH 1))
      (matAdd
        (matScaleB (dnT.scale (XH.2 * XT.2))
          (inertia.headId (ground.sumNat (List.take 1 nsH))
            (ground.getAt 0 nsH 1)))
        (inertia.trailPad (ground.sumNat (List.take 1 nsH))
          (addQ XT (swapQ XH)).1))) :=
  headM_tie diagH offH diagT offH XH XT 1 nsH dnT
    shpH shpT hjH sqXH sqXT hdagT hoffT

/-! The tie at the vacant depth: the two pivots alone, the head
identity at the vacant leading order, and the deviation the whole
pad — the display decided and landed through `headM_tie`. -/

example : matOneValue (matScale XH.2 (headM diagH offH XT 0))
    (matAdd (matScale XT.2 (headM diagH offH XH 0))
      (matAdd
        (matScaleB (dnT.scale (XH.2 * XT.2))
          (inertia.headId (ground.sumNat (List.take 0 nsH))
            (ground.getAt 0 nsH 0)))
        (inertia.trailPad (ground.sumNat (List.take 0 nsH))
          (addQ XT (swapQ XH)).1))) := by decide +kernel

example : matOneValue (matScale XH.2 (headM diagH offH XT 0))
    (matAdd (matScale XT.2 (headM diagH offH XH 0))
      (matAdd
        (matScaleB (dnT.scale (XH.2 * XT.2))
          (inertia.headId (ground.sumNat (List.take 0 nsH))
            (ground.getAt 0 nsH 0)))
        (inertia.trailPad (ground.sumNat (List.take 0 nsH))
          (addQ XT (swapQ XH)).1))) :=
  headM_tie diagH offH diagH offH XH XT 0 nsH dnT shpH shpH
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun i hi => absurd hi (Nat.not_lt_zero i))
    (fun i hi => absurd hi (Nat.not_lt_zero i))

/-! The drift's binder: at a depth-0 diagonal raised by two against
the drift's one the tie hypothesis refuses, and the display refuses
with it. -/

private def diagW : List Mat := [[[⟨7, 1⟩]], [[⟨3, 1⟩]]]

example : ¬ matOneValue (ground.getAt [] diagW 0)
    (matAdd (ground.getAt [] diagH 0)
      (matScaleB dnT (idMat (ground.getAt 0 nsH 0)))) := by decide +kernel

example : ¬ matOneValue (matScale XH.2 (headM diagW offH XT 1))
    (matAdd (matScale XT.2 (headM diagH offH XH 1))
      (matAdd
        (matScaleB (dnT.scale (XH.2 * XT.2))
          (inertia.headId (ground.sumNat (List.take 1 nsH))
            (ground.getAt 0 nsH 1)))
        (inertia.trailPad (ground.sumNat (List.take 1 nsH))
          (addQ XT (swapQ XH)).1))) := by decide +kernel

/-! The couplings' binder: at an occupied shared coupling the tie
display holds, and at the second window's coupling raised off the
first's both the coupling read and the display refuse — the
equal-couplings hypothesis isolated at an occupied instance. -/

private def offO : List Mat := [[[⟨3, 1⟩]]]
private def offO2 : List Mat := [[[⟨4, 1⟩]]]

example : matOneValue (matScale XH.2 (headM diagT offO XT 1))
    (matAdd (matScale XT.2 (headM diagH offO XH 1))
      (matAdd
        (matScaleB (dnT.scale (XH.2 * XT.2))
          (inertia.headId (ground.sumNat (List.take 1 nsH))
            (ground.getAt 0 nsH 1)))
        (inertia.trailPad (ground.sumNat (List.take 1 nsH))
          (addQ XT (swapQ XH)).1))) := by decide +kernel

example : ¬ matOneValue (ground.getAt [] offO2 0)
    (ground.getAt [] offO 0) := by decide +kernel

example : ¬ matOneValue (matScale XH.2 (headM diagT offO2 XT 1))
    (matAdd (matScale XT.2 (headM diagH offO XH 1))
      (matAdd
        (matScaleB (dnT.scale (XH.2 * XT.2))
          (inertia.headId (ground.sumNat (List.take 1 nsH))
            (ground.getAt 0 nsH 1)))
        (inertia.trailPad (ground.sumNat (List.take 1 nsH))
          (addQ XT (swapQ XH)).1))) := by decide +kernel

/-! The tie's display at the equal-membered drift: the two windows
at one diagonal, the leading identity's term at the unit scale and
the cleared pivot difference the whole parting. -/

example : matOneValue (matScale XH.2 (headM diagH offH XT 1))
    (matAdd (matScale XT.2 (headM diagH offH XH 1))
      (matAdd
        (matScaleB (BPair.unit.scale (XH.2 * XT.2))
          (inertia.headId (ground.sumNat (List.take 1 nsH))
            (ground.getAt 0 nsH 1)))
        (inertia.trailPad (ground.sumNat (List.take 1 nsH))
          (addQ XT (swapQ XH)).1))) := by decide +kernel
