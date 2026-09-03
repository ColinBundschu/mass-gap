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
at the occupied drift and at the vacant depth.  The scalar
chain's form read closes the module: `chainQuad` at a two-slab
chain through the theorem beside the decided instance, the shape
read `chainLen` with its length binder's refusal, and the form
read's two shape binders load-bearing — the bond count parted short
refuses with the walked length holding, the two part jointly at the
combined forge — beside the two one-direction partings that satisfy
the display at the padded reads.  Clause (i)'s tail symmetry reads
last: at the chain fixture the fold at the symmetric diagonal reads
every tail pivot symmetric down the recursion, the asymmetric
one-slab seed parting the fold and the conclusion with the
recursion's read standing, and the symmetric diagonal against a
forged member list parting the read with the fold standing.  The
withdrawn term's sandwich closes the module: at the scalar pivot
`X' = 2` with the bond `B = 1` and the witness `R = 1/2` the
withdrawn term `B R` cleared at the two clearings reads
`Rᵀ X' R`, decided raw and through the theorem; and the pivot's
symmetry binder is load-bearing — at the order-two shear
`X' = [[1,2],[0,1]]` with the identity bond and the inverse
witness the witness identity stands while the transpose read
refuses, and the two sides part, `[[1,-2],[0,1]]` against
`[[1,0],[-2,1]]`; and the witness identity is load-bearing in
turn — the forged witness `1` at the symmetric pivot parts the
sandwich at one against two.  The join's form split and the
withdrawn term's cap close the module.  At the pivot `X = 2`, the
bond `B = 2`, the witness `R = 1` and the diagonal `A = 4` the
join reads at the clearings and the form split prices the
diagonal's form as the pivot's joined to the withdrawn term's, four
against two and two, decided and through the theorem, with the
forged diagonal five parting join and display together.  At the
deeper pivot `Xd = 2`, the bond `B = 1` and the witness `R = 1/2`
the floor `(2, 1)` and the bond cap `(1, 1)` are one-sided
comparisons at the kernel-only order-one split, each site datum
vacant so each comparison tight, and the conclusion is tight beside
them at two against two, decided and through the theorem; the three
hypotheses are isolated in turn — the floor forged at `Xd = 1/2`
against the witness two, the bond cap forged at `B = 2`, and the
witness identity forged at `R = 1` — each refused read decided
beside its co-binders' true reads and the conclusion parting with
it, four against one, four against one and two against one.  The
pivots' splits close at a two-member list: the pivots `2` and `−2`
at their order-one splits, the fold's head split, the paired
certificate read at each member, and the prefix's read at the
leading pivot. -/
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

/-! The scalar chain's form read at the two-slab chain
`tridiag(2,1; 1)`: the display's two folds against the walked
vector `(1,2)`, the value `10`. -/

private def cqD : List BPair := [BPair.ofNat 2, BPair.ofNat 1]
private def cqO : List BPair := [BPair.ofNat 1]
private def cqU : List BPair := [BPair.ofNat 1, BPair.ofNat 2]
private def cqRead (d o v : List BPair) : BPair :=
  ground.bsum (fun k =>
      ground.getAt BPair.unit d k
        * (ground.getAt BPair.unit v k * ground.getAt BPair.unit v k))
    (List.range v.length)
  + BPair.ofNat 2
    * ground.bsum (fun k =>
        ground.getAt BPair.unit o k
          * (ground.getAt BPair.unit v k
            * ground.getAt BPair.unit v (k + 1)))
      (List.range o.length)

example : (quadForm
    (assemble (cqD.map (fun a => [[a]])) (cqO.map (fun b => [[b]])))
    cqU).oneValue (BPair.ofNat 10) := by decide +kernel
example : (quadForm
    (assemble (cqD.map (fun a => [[a]])) (cqO.map (fun b => [[b]])))
    cqU).oneValue (cqRead cqD cqO cqU) :=
  chainQuad cqD cqO cqU rfl rfl

/- The two shape binders read load-bearing: the bond count parted
short refuses with the walked length holding, and the two parted
jointly refuse; the two one-direction partings beside them, the
walked vector beyond the diagonal and the bond list at the
diagonal's own count, satisfy the display at the padded reads. -/

example : ¬ ((quadForm
    (assemble
      ([BPair.ofNat 2, BPair.ofNat 1, BPair.ofNat 3].map (fun a => [[a]]))
      (cqO.map (fun b => [[b]])))
    [BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3]).oneValue
    (cqRead [BPair.ofNat 2, BPair.ofNat 1, BPair.ofNat 3] cqO
      [BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3])) := by decide +kernel
example : ¬ ((quadForm
    (assemble (cqD.map (fun a => [[a]]))
      ([BPair.ofNat 1, BPair.ofNat 5].map (fun b => [[b]])))
    [BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3]).oneValue
    (cqRead cqD [BPair.ofNat 1, BPair.ofNat 5]
      [BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3])) := by decide +kernel

example : (quadForm
    (assemble (cqD.map (fun a => [[a]])) (cqO.map (fun b => [[b]])))
    [BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3]).oneValue
    (cqRead cqD cqO [BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3]) := by
  decide +kernel
example : (quadForm
    (assemble (cqD.map (fun a => [[a]]))
      ([BPair.ofNat 1, BPair.ofNat 5].map (fun b => [[b]])))
    cqU).oneValue
    (cqRead cqD [BPair.ofNat 1, BPair.ofNat 5] cqU) := by decide +kernel

example : (assemble (cqD.map (fun a => [[a]]))
      (cqO.map (fun b => [[b]]))).length = 2
    ∧ ((assemble (cqD.map (fun a => [[a]]))
      (cqO.map (fun b => [[b]]))).headD []).length = 2 := by decide +kernel
example : (assemble (cqD.map (fun a => [[a]]))
      (cqO.map (fun b => [[b]]))).length = 2
    ∧ ((assemble (cqD.map (fun a => [[a]]))
      (cqO.map (fun b => [[b]]))).headD []).length = 2 :=
  chainLen cqD cqO rfl
example : ¬ ((assemble ([BPair.ofNat 2].map (fun a => [[a]]))
      ([BPair.ofNat 1, BPair.ofNat 5].map (fun b => [[b]]))).length = 1
    ∧ ((assemble ([BPair.ofNat 2].map (fun a => [[a]]))
      ([BPair.ofNat 1, BPair.ofNat 5].map (fun b => [[b]]))).headD
        []).length = 1) := by decide +kernel

/-! Clause (i)'s tail symmetry at the scalar three-slab chain: the
fold at the symmetric diagonal reads every tail pivot symmetric
down the recursion, the theorem route beside the seed pivot's own
decided read. -/

example : ∀ i, i < xs3.length →
    matOneValue (transposeM (ground.getAt dM xs3 i).1)
      (ground.getAt dM xs3 i).1 :=
  greenprod.tailSym diag3 off3 xs3 rs3 [1, 1, 1]
    (by decide +kernel) (by decide +kernel)

example : matOneValue (transposeM (ground.getAt dM xs3 0).1)
    (ground.getAt dM xs3 0).1 := by decide +kernel

/-! The symmetry fold's own refusal: the one-slab seed
`A = [[1,1],[0,1]]` reads the recursion at `X = A` while the fold
refuses at that diagonal, and the conclusion parts at the seed
pivot. -/

private def asymA : Mat := [[⟨2, 1⟩, ⟨2, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]

example : tailRead [asymA] [] [(asymA, 1)] [] [2] := by decide +kernel
example : ¬ (((List.range ([asymA] : List Mat).length).all
    (fun i => decide (matOneValue
      (transposeM (ground.getAt [] [asymA] i))
      (ground.getAt [] [asymA] i)))) = true) := by decide +kernel
example : ¬ matOneValue
    (transposeM (ground.getAt dM [((asymA, 1) : MatQ)] 0).1)
    (ground.getAt dM [((asymA, 1) : MatQ)] 0).1 := by decide +kernel

/-! The recursion's own refusal: the symmetric diagonal
`A = [[1,0],[0,1]]` against the forged member list parts the
recursion at the seed while its fold stands, the conclusion the
parting above. -/

private def symA : Mat := [[⟨2, 1⟩, u], [u, ⟨2, 1⟩]]

example : ¬ tailRead [symA] [] [(asymA, 1)] [] [2] := by decide +kernel
example : ((List.range ([symA] : List Mat).length).all
    (fun i => decide (matOneValue
      (transposeM (ground.getAt [] [symA] i))
      (ground.getAt [] [symA] i)))) = true := by decide +kernel

/-! Clause (i)'s withdrawn term at the scalar pivot: the deeper
pivot `X' = 2` at the unit clearing, the bond `B = 1` and the
witness `R = 1/2` — the witness identity `X'R = Bᵀ` holds at the
clearings, and the withdrawn term `B R` cleared at `X'`'s and
`R`'s clearings reads the sandwich `Rᵀ X' R`, decided raw and
through the theorem. -/

private def wsXp : MatQ := ([[⟨3, 1⟩]], 1)
private def wsB : Mat := [[⟨2, 1⟩]]
private def wsR : MatQ := ([[⟨2, 1⟩]], 2)

example : oneValueQ (mulQ wsXp wsR) (ofM (transposeM wsB)) := by
  decide +kernel

example : matOneValue (matScale (wsXp.2 * wsR.2) (matMul wsB wsR.1))
    (matMul (matMul (transposeM wsR.1) wsXp.1) wsR.1) := by
  decide +kernel

example : matOneValue (matScale (wsXp.2 * wsR.2) (matMul wsB wsR.1))
    (matMul (matMul (transposeM wsR.1) wsXp.1) wsR.1) :=
  withdrawn_sandwich (k := 1) (k' := 1) wsXp wsR wsB
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! The withdrawn term's symmetry binder, isolated at the
order-two shear: the deeper pivot `X' = [[1,2],[0,1]]` at the unit
clearing, the bond the identity and the witness the pivot's own
inverse `[[1,-2],[0,1]]`.  The witness identity `X'R = Bᵀ = I`
stands while the pivot's transpose read refuses, and the two sides
of the sandwich part — `[[1,-2],[0,1]]` against
`[[1,0],[-2,1]]`. -/

private def waXp : MatQ := ([[⟨2, 1⟩, ⟨3, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], 1)
private def waB : Mat := [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]
private def waR : MatQ := ([[⟨2, 1⟩, ⟨1, 3⟩], [⟨1, 1⟩, ⟨2, 1⟩]], 1)

example : oneValueQ (mulQ waXp waR) (ofM (transposeM waB)) := by
  decide +kernel
example : ¬ matOneValue (transposeM waXp.1) waXp.1 := by decide +kernel
example : ¬ matOneValue (matScale (waXp.2 * waR.2) (matMul waB waR.1))
    (matMul (matMul (transposeM waR.1) waXp.1) waR.1) := by
  decide +kernel

/-! The withdrawn term's witness identity, isolated: at the deeper
pivot `2` with the bond `1` and the forged witness `1`, the pivot's
symmetry and every shape stand while the witness identity refuses,
and the sandwich's two sides part at one against two. -/

private def wwR : MatQ := ([[⟨2, 1⟩]], 1)

example : ¬ oneValueQ (mulQ wsXp wwR) (ofM (transposeM wsB)) := by
  decide +kernel
example : matOneValue (transposeM wsXp.1) wsXp.1 := by decide +kernel
example : ¬ matOneValue (matScale (wsXp.2 * wwR.2) (matMul wsB wwR.1))
    (matMul (matMul (transposeM wwR.1) wsXp.1) wwR.1) := by
  decide +kernel

/-! Clause (i)'s join at the scalar slab: the pivot `X = 2` at the
unit clearing, the bond `B = 2`, the witness `R = 1` and the
diagonal `A = 4` — the join `X + B R = A` reads at the clearings,
and the form split prices the diagonal's form as the pivot's joined
to the withdrawn term's, four against two and two, decided raw and
through the theorem; the forged diagonal `A = 5` parts the
join and the display beside it. -/

private def jqX : MatQ := ([[⟨3, 1⟩]], 1)
private def jqR : MatQ := ([[⟨2, 1⟩]], 1)
private def jqB : Mat := [[⟨3, 1⟩]]
private def jqA : Mat := [[⟨5, 1⟩]]
private def jqV : List BPair := [⟨2, 1⟩]

example : oneValueQ (addQ jqX (mulQ (ofM jqB) jqR)) (ofM jqA) := by
  decide +kernel

example : ((quadForm jqA jqV).scale (jqX.2 * jqR.2)).oneValue
    ((quadForm jqX.1 jqV).scale jqR.2
      + (quadForm (matMul jqB jqR.1) jqV).scale jqX.2) := by
  decide +kernel

example : ∀ w : List BPair, w.length = 1 →
    ((quadForm jqA w).scale (jqX.2 * jqR.2)).oneValue
      ((quadForm jqX.1 w).scale jqR.2
        + (quadForm (matMul jqB jqR.1) w).scale jqX.2) :=
  join_quadSplit (o := 1) (o' := 1) jqX jqR jqA jqB
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- Refusal naming the join's own binder: at the diagonal five the
join refuses at the clearings and the form split parts beside it,
five against the pivot's two joined to the withdrawn term's two. -/

private def jqA' : Mat := [[⟨6, 1⟩]]

example : ¬ oneValueQ (addQ jqX (mulQ (ofM jqB) jqR)) (ofM jqA') := by
  decide +kernel
example : ¬ ((quadForm jqA' jqV).scale (jqX.2 * jqR.2)).oneValue
    ((quadForm jqX.1 jqV).scale jqR.2
      + (quadForm (matMul jqB jqR.1) jqV).scale jqX.2) := by
  decide +kernel

/-! The withdrawn term's cap at the arriving floor: the deeper
pivot `Xd = 2` at the unit clearing, the bond `B = 1` and the
witness `R = 1/2` at the witness identity `Xd R = Bᵀ`.  The floor
`(2, 1)` and the bond cap `(1, 1)` are the one-sided comparisons at
the kernel-only order-one split — each site datum reads the vacant
entry, so each comparison is tight — and the conclusion is tight
beside them, the withdrawn term's form scaled by the floor's
numerator against the bond's denominator reading two against the
self-pairing scaled by the bond's numerator against the floor's
denominator and the witness clearing. -/

private def scXd : MatQ := ([[⟨3, 1⟩]], 1)
private def scB : Mat := [[⟨2, 1⟩]]
private def scR : MatQ := ([[⟨2, 1⟩]], 2)
private def scV : List BPair := [⟨2, 1⟩]

/-- The kernel-only order-one split at the identity congruence, the
tight comparisons' shared certificate. -/
private def scKsp : Split 1 :=
  ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [], 1, rfl⟩

example : oneValueQ (mulQ scXd scR) (ofM (transposeM scB)) := by
  decide +kernel

example : leAt (matScale (2 * scXd.2) (idMat 1))
    (matScale 1 scXd.1) scKsp := by decide +kernel

example : leAt (matScale 1 (matMul scB (transposeM scB)))
    (matScale 1 (idMat 1)) scKsp := by decide +kernel

private theorem scFloor : ∀ w : List BPair, w.length = 1 →
    (dotN w w).scale (2 * scXd.2) ≤ (quadForm scXd.1 w).scale 1 :=
  fun w hw =>
    ground.leB_congr
      (BPair.oneValue_trans
        (quadForm_scale (2 * scXd.2) (idMat 1) w)
        (BPair.scale_congr (2 * scXd.2)
          (dotN_congrR w _ _ (matVec_idMat 1 w hw))))
      (quadForm_scale 1 scXd.1 w)
      (le_all (matScale (2 * scXd.2) (idMat 1)) (matScale 1 scXd.1)
        scKsp (by decide +kernel) (by decide +kernel)
        (by decide +kernel) w hw)

private theorem scBond : ∀ w : List BPair, w.length = 1 →
    (quadForm (matMul scB (transposeM scB)) w).scale 1
      ≤ (dotN w w).scale 1 :=
  fun w hw =>
    ground.leB_congr
      (quadForm_scale 1 (matMul scB (transposeM scB)) w)
      (BPair.oneValue_trans (quadForm_scale 1 (idMat 1) w)
        (BPair.scale_congr 1 (dotN_congrR w _ _ (matVec_idMat 1 w hw))))
      (le_all (matScale 1 (matMul scB (transposeM scB)))
        (matScale 1 (idMat 1)) scKsp (by decide +kernel)
        (by decide +kernel) (by decide +kernel) w hw)

example : (quadForm (matMul scB scR.1) scV).scale (2 * 1)
    ≤ (dotN scV scV).scale (1 * (1 * scR.2)) := by decide +kernel

example : ∀ w : List BPair, w.length = 1 →
    (quadForm (matMul scB scR.1) w).scale (2 * 1)
      ≤ (dotN w w).scale (1 * (1 * scR.2)) :=
  sandwich_cap (o := 1) (o' := 1) scXd scR scB 2 1 1 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    scFloor scBond

/-- Refusal isolating the arriving floor: at the deeper pivot
`Xd = 1/2` with the witness `R = 2` the witness identity and the
bond cap stand, while the floor `(2, 1)` reads four against one and
the conclusion parts beside it, four against one. -/

private def sfXd : MatQ := ([[⟨2, 1⟩]], 2)
private def sfR : MatQ := ([[⟨3, 1⟩]], 1)

example : oneValueQ (mulQ sfXd sfR) (ofM (transposeM scB)) := by
  decide +kernel
example : (quadForm (matMul scB (transposeM scB)) scV).scale 1
    ≤ (dotN scV scV).scale 1 := by decide +kernel
example : ¬ ((dotN scV scV).scale (2 * sfXd.2)
    ≤ (quadForm sfXd.1 scV).scale 1) := by decide +kernel
example : ¬ ((quadForm (matMul scB sfR.1) scV).scale (2 * 1)
    ≤ (dotN scV scV).scale (1 * (1 * sfR.2))) := by decide +kernel

/-- Refusal isolating the bond's square cap: at the bond `B = 2`
with the witness `R = 1` the witness identity and the floor stand,
while the bond cap `(1, 1)` reads four against one and the
conclusion parts beside it, four against one. -/

private def scRu : MatQ := ([[⟨2, 1⟩]], 1)
private def sbB : Mat := [[⟨3, 1⟩]]

example : oneValueQ (mulQ scXd scRu) (ofM (transposeM sbB)) := by
  decide +kernel
example : (dotN scV scV).scale (2 * scXd.2)
    ≤ (quadForm scXd.1 scV).scale 1 := by decide +kernel
example : ¬ ((quadForm (matMul sbB (transposeM sbB)) scV).scale 1
    ≤ (dotN scV scV).scale 1) := by decide +kernel
example : ¬ ((quadForm (matMul sbB scRu.1) scV).scale (2 * 1)
    ≤ (dotN scV scV).scale (1 * (1 * scRu.2))) := by decide +kernel

/-- Refusal isolating the witness identity: at the pass fixture's
pivot and bond with the witness `R = 1` the floor and the bond cap
stand, while the witness identity reads two against the bond's
transpose one and the conclusion parts beside it, two against
one. -/

example : ¬ oneValueQ (mulQ scXd scRu) (ofM (transposeM scB)) := by
  decide +kernel
example : (quadForm (matMul scB (transposeM scB)) scV).scale 1
    ≤ (dotN scV scV).scale 1 := by decide +kernel
example : ¬ ((quadForm (matMul scB scRu.1) scV).scale (2 * 1)
    ≤ (dotN scV scV).scale (1 * (1 * scRu.2))) := by decide +kernel

/-! The pivots' splits at the two-member list: the pivots `2` and
`−2` at their order-one splits, the fold reading the head's count
joined to the tail's, the paired certificate read at each member,
and the prefix's own read at the leading pivot. -/

private def rlSp (a : BPair) : Split 1 :=
  ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one a], 0, rfl⟩
private def rlXs : List MatQ := [([[⟨3, 1⟩]], 1), ([[⟨1, 3⟩]], 1)]
private def rlSps : List ((k : Nat) × Split k) :=
  [⟨1, rlSp ⟨3, 1⟩⟩, ⟨1, rlSp ⟨1, 3⟩⟩]

example : revListRead rlXs rlSps := by decide +kernel
example : revFold rlSps = 1 := by decide +kernel
example : revFold rlSps
    = revAt (rlSp ⟨3, 1⟩) + revFold [⟨1, rlSp ⟨1, 3⟩⟩] :=
  revFold_cons ⟨1, rlSp ⟨3, 1⟩⟩ [⟨1, rlSp ⟨1, 3⟩⟩]

example : splitRead (ground.getAt dM rlXs 1).1
    (ground.getAt ⟨1, rlSp ⟨3, 1⟩⟩ rlSps 1).2 := by decide +kernel
example : ∀ i, i < rlXs.length →
    ∀ d : (k : Nat) × Split k,
      splitRead (ground.getAt dM rlXs i).1 (ground.getAt d rlSps i).2 :=
  revListRead_at rlXs rlSps (by decide +kernel)

example : revListRead (rlXs.take 1) (rlSps.take 1) := by decide +kernel
example : revListRead (rlXs.take 1) (rlSps.take 1) :=
  revListRead_take rlXs rlSps 1 (by decide +kernel)

/-! The withdrawn term's cap at two orders: the deeper pivot
`diag(1, 2)`, the bond `[[1, 1], [0, 1]]` and the witness
`[[2, 0], [1, 1]]` at the clearing two, the witness identity read
whole; the floor `(1, 1)` at the site datum `diag(0, 1)` under the
exchanging congruence, the bond's square `[[2, 1], [1, 1]]` capped
at `(3, 1)` under the unit-triangular congruence, and the squared
pairing strict at the two orders, the conclusion at six against
twelve. -/

private def q2Xd : MatQ :=
  ([[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨3, 1⟩]], 1)
private def q2B : Mat := [[⟨2, 1⟩, ⟨2, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]
private def q2R : MatQ :=
  ([[⟨3, 1⟩, ⟨1, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]], 2)
private def q2V : List BPair := [⟨2, 1⟩, ⟨2, 1⟩]

/-- The floor's split: the exchanging congruence reads the site
datum `diag(0, 1)` at its occupied entry over the kernel. -/
private def q2FSp : Split 2 :=
  ⟨⟨[[⟨1, 1⟩, ⟨1, 2⟩], [⟨2, 1⟩, ⟨1, 1⟩]], rfl⟩,
   ⟨[[⟨1, 1⟩, ⟨2, 1⟩], [⟨1, 2⟩, ⟨1, 1⟩]], rfl⟩,
   [.one ⟨2, 1⟩], 1, rfl⟩

/-- The bond cap's split: the unit-triangular congruence at the
datum `[[1, -1], [-1, 2]]`, two occupied entries. -/
private def q2BSp : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨2, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨1, 2⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨2, 1⟩, .one ⟨2, 1⟩], 0, rfl⟩

example : oneValueQ (mulQ q2Xd q2R) (ofM (transposeM q2B)) := by
  decide +kernel

example : leAt (matScale (1 * q2Xd.2) (idMat 2))
    (matScale 1 q2Xd.1) q2FSp := by decide +kernel

example : leAt (matScale 1 (matMul q2B (transposeM q2B)))
    (matScale 3 (idMat 2)) q2BSp := by decide +kernel

private theorem q2Floor : ∀ w : List BPair, w.length = 2 →
    (dotN w w).scale (1 * q2Xd.2) ≤ (quadForm q2Xd.1 w).scale 1 :=
  fun w hw =>
    ground.leB_congr
      (BPair.oneValue_trans
        (quadForm_scale (1 * q2Xd.2) (idMat 2) w)
        (BPair.scale_congr (1 * q2Xd.2)
          (dotN_congrR w _ _ (matVec_idMat 2 w hw))))
      (quadForm_scale 1 q2Xd.1 w)
      (le_all (matScale (1 * q2Xd.2) (idMat 2)) (matScale 1 q2Xd.1)
        q2FSp (by decide +kernel) (by decide +kernel)
        (by decide +kernel) w hw)

private theorem q2Bond : ∀ w : List BPair, w.length = 2 →
    (quadForm (matMul q2B (transposeM q2B)) w).scale 1
      ≤ (dotN w w).scale 3 :=
  fun w hw =>
    ground.leB_congr
      (quadForm_scale 1 (matMul q2B (transposeM q2B)) w)
      (BPair.oneValue_trans (quadForm_scale 3 (idMat 2) w)
        (BPair.scale_congr 3 (dotN_congrR w _ _ (matVec_idMat 2 w hw))))
      (le_all (matScale 1 (matMul q2B (transposeM q2B)))
        (matScale 3 (idMat 2)) q2BSp (by decide +kernel)
        (by decide +kernel) (by decide +kernel) w hw)

example : (dotN (matVec q2R.1 q2V) (matVec (transposeM q2B) q2V))
      * (dotN (matVec q2R.1 q2V) (matVec (transposeM q2B) q2V))
    < (dotN (matVec q2R.1 q2V) (matVec q2R.1 q2V))
      * (dotN (matVec (transposeM q2B) q2V)
          (matVec (transposeM q2B) q2V)) := by decide +kernel

example : (quadForm (matMul q2B q2R.1) q2V).scale (1 * 1)
    ≤ (dotN q2V q2V).scale (3 * (1 * q2R.2)) := by decide +kernel

example : ∀ w : List BPair, w.length = 2 →
    (quadForm (matMul q2B q2R.1) w).scale (1 * 1)
      ≤ (dotN w w).scale (3 * (1 * q2R.2)) :=
  sandwich_cap (o := 2) (o' := 2) q2Xd q2R q2B 1 1 3 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    q2Floor q2Bond

/-! ## The chain chart

The scalar chain's entry chart at the diagonal `(2, 3, 4)` and the
bonds `(5, 6)`: the four reads decided at the chart, the assembled
chain's entries read through `chainEntry` beside the decided cells,
the bond count's short side load-bearing (one bond at three diagonal
entries drops the last slab, the corner entry reading the sum's unit
against the chart's `4`), and its long side the padded read (a third
bond beyond the last slab widens the assembled rows past the order,
every entry inside the order the chart's own). -/

private def cd : List BPair := [⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩]
private def co : List BPair := [⟨5, 1⟩, ⟨6, 1⟩]
private def coShort : List BPair := [⟨5, 1⟩]
private def coLong : List BPair := [⟨5, 1⟩, ⟨6, 1⟩, ⟨7, 1⟩]

example : chainAt cd co 1 1 = ⟨3, 1⟩ := by decide +kernel
example : chainAt cd co 1 2 = ⟨6, 1⟩ := by decide +kernel
example : chainAt cd co 2 1 = ⟨6, 1⟩ := by decide +kernel
example : chainAt cd co 0 2 = BPair.unit := by decide +kernel
example : chainAt cd co 1 1 = ⟨3, 1⟩ :=
  (chainAt_diag cd co 1).trans (by decide +kernel)
example : chainAt cd co 1 2 = ⟨6, 1⟩ :=
  (chainAt_up cd co 1 2 (by decide +kernel) (by decide +kernel) rfl).trans
    (by decide +kernel)

example : ground.getAt BPair.unit (ground.getAt []
    (assemble (cd.map (fun x => [[x]])) (co.map (fun x => [[x]]))) 1) 2
    = chainAt cd co 1 2 := by decide +kernel
example : ground.getAt BPair.unit (ground.getAt []
    (assemble (cd.map (fun x => [[x]])) (co.map (fun x => [[x]]))) 1) 2
    = chainAt cd co 1 2 :=
  chainEntry cd co rfl 1 2 (by decide +kernel) (by decide +kernel)
example : ground.getAt BPair.unit (ground.getAt []
    (assemble (cd.map (fun x => [[x]])) (co.map (fun x => [[x]]))) 2) 2
    = chainAt cd co 2 2 :=
  chainEntry cd co rfl 2 2 (by decide +kernel) (by decide +kernel)

/-- The bond count's short side is load-bearing: at one bond the
assembled chain drops its last slab and the corner entry reads the
sum's unit against the chart's `4`. -/
example : ¬ (ground.getAt BPair.unit (ground.getAt []
    (assemble (cd.map (fun x => [[x]])) (coShort.map (fun x => [[x]]))) 2) 2
    = chainAt cd coShort 2 2) := by decide +kernel

/-- The long side is the padded read: at three bonds the entries
inside the order stay the chart's own. -/
example : ground.getAt BPair.unit (ground.getAt []
    (assemble (cd.map (fun x => [[x]])) (coLong.map (fun x => [[x]]))) 2) 1
    = chainAt cd coLong 2 1 := by decide +kernel
example : ¬ (coLong.length + 1 = cd.length) := by decide +kernel
