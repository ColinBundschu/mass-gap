import MassGap.Spectator
/-!
The check module for `lem:spectator`: the batteries re-read the
spectator law by kernel `decide` at the two scalar three-slab
families `tridiag(3,3,3; 1,1)` and `tridiag(2,3,3; 1,1)`, the
perturbation at the first slab.  Clause (i): the tail pivots equal
beyond the perturbation (`X = (21/8, 8/3, 3)` against
`(13/8, 8/3, 3)`), and the deviation sandwich telescoping exactly,
`D = (-1, -1/6, -1/40)` at the transfer factors, with the
forged-deviation refusal; the reversed slab order reads the same
law at the pair `tridiag(3,3,3; 1,1)` and `tridiag(3,3,4; 1,1)`,
the perturbation at the last slab — the head pivots `3, 8/3` equal
below it and the tail deviation `E = (1/88, 1/12, 1)` sandwiched
down to the head at the tail transfer factors, both reversed reads
parting at the head-perturbed pair.  Clause (ii): the cap step at the
contraction certificates `λ = 1/3`, `λ' = 1/2` — the deviation
capped at the deeper slab's block and the doubled next deviation at
`13/36` of the step's own — beside the step at two blocks of
crossing orders.
Clause (iii): the walk's cleared bulk datum `(A, B) = (5, 2)` — the
deck polynomial `2z² - 5z + 2` with its symmetry, the interior
solvent `X = 1/2` with the off-root refusal, the pivot pair
`Y = 4`, the pivot map's fixed point, and the exact factorization
`(4z - 8)(2z - 1) = 4 (2z² - 5z + 2)`; the two-by-two deck
polynomial `det((z²-2z+1) I - z E₁₂ - z E₂₁)` symmetric at
`[1, -4, 5, -4, 1]`.  The ball tier at that datum: the floor at
the center `Ŷ = 4` with `(y0 + ρ) G = 4` and the forged floor
`y0 = 5` refusing at the site datum `-2`; the ball certificate at
`λ = 1/2`, `y0 = 3`, `ρ = 1`, `ρ0 = 1/2`, `λ∘ = 2/3`, with the
isolating refusals at the forged tie `λ∘ = 1/3`, the starved
contraction `λ = 1/3`, the forged witness `Cc = 1/3` (both pivot
identities parting), the modulus read `ρ0 = 2/3`, and the two
displays' own refusals at the forged image and the forged pivot;
the membership walk at the pivots `5, 21/5, 85/21` around the
center `4` with the tightened radius `1/2` refusing at the head;
the ball's positivity through `ball_psd` at the tail pivot `5`,
the theorem route at the stated splits; and one cap step walked
at the two families' brackets, the length forgery refusing at the
vacant certificate list.  The tied slab order at two windows: the
drift `δ = 1` at the tie `A'_i = A_i + 1` below the perturbation
slab `w0 = 2`, the second window `tridiag(4,4,5; 1,1)` at its tail
pivots `(71/19, 19/5, 5)` and witnesses `(5/19, 1/5)`, the tied
step's identity, the tie datum's identity capped at each step's own
slab block, and the two-step walk folding the seed pair `2` to
`23305382/20793600` with the depth-`0` deviation `169/152` read
inside it through `driftShare_cap`; the binder records at the tie,
the tied step, the seed pair, the depth and the source cap; the
equal-membered tie at `δ` the sum's unit reading the committed
reversed pair; and the tied walk at a gap of varying orders
`ns = [1, 2, 1]`, the two steps crossing the orders from the seed
pair `2` to the folded pair `[34 : 4]` with the depth-`0`
deviation inside it, beside the refusals at the gram list's own
orders and at the root factor's forged pair. -/
set_option maxHeartbeats 4000000

open ground poly elim inertia greenprod spectator

private def u : BPair := BPair.unit

/-! The two families and their recursion data. -/

private def diag3 : List Mat := [[[⟨4, 1⟩]], [[⟨4, 1⟩]], [[⟨4, 1⟩]]]
private def diag3' : List Mat := [[[⟨3, 1⟩]], [[⟨4, 1⟩]], [[⟨4, 1⟩]]]
private def off3 : List Mat := [[[⟨2, 1⟩]], [[⟨2, 1⟩]]]
private def xs3 : List MatQ :=
  [([[⟨22, 1⟩]], 8), ([[⟨9, 1⟩]], 3), ([[⟨4, 1⟩]], 1)]
private def rs3 : List MatQ := [([[⟨4, 1⟩]], 8), ([[⟨2, 1⟩]], 3)]
private def xs3' : List MatQ :=
  [([[⟨14, 1⟩]], 8), ([[⟨9, 1⟩]], 3), ([[⟨4, 1⟩]], 1)]
private def ys3 : List MatQ :=
  [([[⟨4, 1⟩]], 1), ([[⟨9, 1⟩]], 3), ([[⟨22, 1⟩]], 8)]
private def cs3 : List MatQ := [([[⟨2, 1⟩]], 3), ([[⟨4, 1⟩]], 8)]
private def ys3' : List MatQ :=
  [([[⟨3, 1⟩]], 1), ([[⟨6, 1⟩]], 2), ([[⟨14, 1⟩]], 5)]
private def cs3' : List MatQ := [([[⟨2, 1⟩]], 2), ([[⟨3, 1⟩]], 5)]

/-! Clause (i): the shared tail and the deviation sandwich. -/

example : tailShareRead diag3 off3 diag3' off3 xs3 rs3 xs3' rs3
    0 [1, 1, 1] := by decide +kernel
example : sandwichRead diag3 off3 diag3' off3 ys3 cs3 ys3' cs3'
    0 [1, 1, 1] := by decide +kernel
example : sandwichStep ([[⟨2, 1⟩]], 3) ([[⟨2, 1⟩]], 2)
    ([[⟨6, 1⟩]], 2) ([[⟨9, 1⟩]], 3) ([[⟨3, 1⟩]], 1)
    ([[⟨4, 1⟩]], 1) 1 1 := by decide +kernel
example : ¬ sandwichStep ([[⟨2, 1⟩]], 3) ([[⟨2, 1⟩]], 2)
    ([[⟨7, 1⟩]], 2) ([[⟨9, 1⟩]], 3) ([[⟨3, 1⟩]], 1)
    ([[⟨4, 1⟩]], 1) 1 1 := by decide +kernel

/-! Clause (i) at the reversed slab order: the third family
`tridiag(3,3,4; 1,1)` perturbed at the last slab, the shared depth
`w0 = 2`.  The head pivots `3, 8/3` agree below that slab and part
at `21/8` against `29/8` above it; the tail deviation
`E = (1/88, 1/12, 1)` telescopes down to the head at the tail
transfer factors, `E_2 = (1/3) E_3 (1/4)` and
`E_1 = (3/8) E_2 (4/11)`.  The head-perturbed family parts both
reversed reads — the tail sandwich at the slab data below the
perturbation, the head share at the first head pivot. -/

private def diagV : List Mat := [[[⟨4, 1⟩]], [[⟨4, 1⟩]], [[⟨5, 1⟩]]]
private def xsV : List MatQ :=
  [([[⟨30, 1⟩]], 11), ([[⟨12, 1⟩]], 4), ([[⟨5, 1⟩]], 1)]
private def rsV : List MatQ := [([[⟨5, 1⟩]], 11), ([[⟨2, 1⟩]], 4)]
private def ysV : List MatQ :=
  [([[⟨4, 1⟩]], 1), ([[⟨9, 1⟩]], 3), ([[⟨30, 1⟩]], 8)]
private def csV : List MatQ := [([[⟨2, 1⟩]], 3), ([[⟨4, 1⟩]], 8)]

example : headShareRead diag3 off3 diagV off3 ys3 cs3 ysV csV
    2 [1, 1, 1] := by decide +kernel
example : tailSandwichRead diag3 off3 diagV off3 xs3 rs3 xsV rsV
    2 [1, 1, 1] := by decide +kernel
example : ¬ tailSandwichRead diag3 off3 diag3' off3 xs3 rs3 xs3' rs3
    2 [1, 1, 1] := by decide +kernel
example : ¬ headShareRead diag3 off3 diag3' off3 ys3 cs3 ys3' cs3'
    2 [1, 1, 1] := by decide +kernel

/-! Clause (ii): the cap step at the contraction certificates. -/

private def spK : Split 1 := ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [], 1, rfl⟩
private def spOne (a : BPair) : Split 1 :=
  ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one a], 0, rfl⟩
private def sp2p : Split 1 := spOne ⟨3, 1⟩
private def spU' : Split 1 := spOne ⟨151, 1⟩
private def spL' : Split 1 := spOne ⟨7, 1⟩

example : contractRead (transfer ([[⟨2, 1⟩]], 3)) [[⟨2, 1⟩]] [[⟨2, 1⟩]]
    1 3 spK := by decide +kernel
example : capQ (devQ ([[⟨3, 1⟩]], 1) ([[⟨4, 1⟩]], 1)) [[⟨2, 1⟩]]
    1 1 sp2p spK := by decide +kernel
example : capStepRead ([[⟨2, 1⟩]], 3) ([[⟨2, 1⟩]], 2)
    ([[⟨6, 1⟩]], 2) ([[⟨9, 1⟩]], 3) ([[⟨3, 1⟩]], 1) ([[⟨4, 1⟩]], 1)
    [[⟨2, 1⟩]] [[⟨2, 1⟩]] 1 1 1 3 1 2 spK spK sp2p spK spU'
    spL' := by decide +kernel

/-! Clause (iii): the walk's cleared bulk datum `(A, B) = (5, 2)`,
and the two-by-two deck symmetry. -/

example : poly.oneValue (deckPoly [[⟨6, 1⟩]] [[⟨3, 1⟩]])
    [⟨3, 1⟩, ⟨1, 6⟩, ⟨3, 1⟩] := by decide +kernel
example : deckfactor.deckSymRead (deckPoly [[⟨6, 1⟩]] [[⟨3, 1⟩]])
    1 := by decide +kernel
example : solventRead ([[⟨2, 1⟩]], 2) [[⟨6, 1⟩]] [[⟨3, 1⟩]] 1 := by
  decide +kernel
example : ¬ solventRead ([[⟨2, 1⟩]], 1) [[⟨6, 1⟩]] [[⟨3, 1⟩]] 1 := by
  decide +kernel
example : pivotPairRead ([[⟨5, 1⟩]], 1) ([[⟨2, 1⟩]], 2) [[⟨6, 1⟩]]
    [[⟨3, 1⟩]] 1 := by decide +kernel
example : pivotStepRead ([[⟨5, 1⟩]], 1) ([[⟨2, 1⟩]], 2)
    ([[⟨5, 1⟩]], 1) [[⟨6, 1⟩]] [[⟨3, 1⟩]] 1 := by decide +kernel
example : facSplitRead ([[⟨2, 1⟩]], 2) [[⟨6, 1⟩]] [[⟨3, 1⟩]] 1 := by
  decide +kernel
example : poly.oneValue
    (deckPoly [[⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨3, 1⟩]]
      [[⟨2, 1⟩, u], [u, ⟨2, 1⟩]])
    [⟨2, 1⟩, ⟨1, 5⟩, ⟨6, 1⟩, ⟨1, 5⟩, ⟨2, 1⟩] := by decide +kernel
example : deckfactor.deckSymRead
    (deckPoly [[⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨3, 1⟩]]
      [[⟨2, 1⟩, u], [u, ⟨2, 1⟩]]) 2 := by decide +kernel

/-! The ball tier at the bulk datum's fixed point: the floor, the
ball certificate with its modulus data and the per-conjunct
isolating refusals, the membership walk, and the cap chain. -/

example : floorRead ([[⟨5, 1⟩]], 1) [[⟨2, 1⟩]] 3 1 1 1 spK := by decide +kernel
example : splitRead (siteDatum (matScale (1 * 1) ([[⟨5, 1⟩]] : Mat))
    (matScale (1 * (5 * 1 + 1 * 1)) [[⟨2, 1⟩]])) (spOne ⟨1, 3⟩) := by
  decide +kernel
example : ¬ floorRead ([[⟨5, 1⟩]], 1) [[⟨2, 1⟩]] 5 1 1 1
    (spOne ⟨1, 3⟩) := by decide +kernel

example : ballRead ([[⟨5, 1⟩]], 1) ([[⟨2, 1⟩]], 2) ([[⟨5, 1⟩]], 1)
    [[⟨6, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 1 2 3 1 1 1 1 2 2 3
    spK spK (spOne ⟨2, 1⟩) (spOne ⟨2, 1⟩) := by decide +kernel
example : ¬ ballRead ([[⟨5, 1⟩]], 1) ([[⟨2, 1⟩]], 2) ([[⟨5, 1⟩]], 1)
    [[⟨6, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 1 2 3 1 1 1 1 2 1 3
    spK spK (spOne ⟨2, 1⟩) (spOne ⟨2, 1⟩) := by decide +kernel
example : ¬ ballRead ([[⟨5, 1⟩]], 1) ([[⟨2, 1⟩]], 2) ([[⟨5, 1⟩]], 1)
    [[⟨6, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 1 3 3 1 1 1 1 2 4 9
    spK spK (spOne ⟨2, 1⟩) (spOne ⟨2, 1⟩) := by decide +kernel
example : ¬ ballRead ([[⟨5, 1⟩]], 1) ([[⟨2, 1⟩]], 3) ([[⟨5, 1⟩]], 1)
    [[⟨6, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 1 2 3 1 1 1 1 2 2 3
    (spOne ⟨6, 1⟩) spK (spOne ⟨2, 1⟩) (spOne ⟨2, 1⟩) := by decide +kernel
example : ¬ pivotStepRead ([[⟨5, 1⟩]], 1) ([[⟨2, 1⟩]], 2)
    ([[⟨6, 1⟩]], 1) [[⟨6, 1⟩]] [[⟨3, 1⟩]] 1 := by decide +kernel
example : ¬ pivotPairRead ([[⟨4, 1⟩]], 1) ([[⟨2, 1⟩]], 2)
    [[⟨6, 1⟩]] [[⟨3, 1⟩]] 1 := by decide +kernel
example : capQ (devQ ([[⟨5, 1⟩]], 1) ([[⟨5, 1⟩]], 1)) [[⟨2, 1⟩]] 2 3
    sp2p sp2p := by decide +kernel
example : ¬ ballRead ([[⟨5, 1⟩]], 1) ([[⟨2, 1⟩]], 2) ([[⟨5, 1⟩]], 1)
    [[⟨6, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 1 2 3 1 1 1 2 3 2 3
    spK spK sp2p sp2p := by decide +kernel

example : ballList ([[⟨5, 1⟩]], 1) [[⟨2, 1⟩]] 1 1
    [([[⟨6, 1⟩]], 1), ([[⟨22, 1⟩]], 5), ([[⟨86, 1⟩]], 21)]
    [(spK, sp2p), (spOne ⟨5, 1⟩, spOne ⟨7, 1⟩),
     (spOne ⟨21, 1⟩, spOne ⟨23, 1⟩)] := by decide +kernel
example : ¬ ballList ([[⟨5, 1⟩]], 1) [[⟨2, 1⟩]] 1 2
    [([[⟨6, 1⟩]], 1), ([[⟨22, 1⟩]], 5), ([[⟨86, 1⟩]], 21)]
    [(spK, sp2p), (spOne ⟨5, 1⟩, spOne ⟨7, 1⟩),
     (spOne ⟨21, 1⟩, spOne ⟨23, 1⟩)] := by decide +kernel

/-! The ball's positivity at the walk's tail pivot, the theorem
route: the center's floor and the deviation's cap read the pivot's
split at the upper side. -/

example : psdAt (spOne ⟨6, 1⟩) :=
  ball_psd ([[⟨6, 1⟩]], 1) ([[⟨5, 1⟩]], 1) [[⟨2, 1⟩]] 3 1 1 1
    spK spK sp2p (spOne ⟨6, 1⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! `ball_psd`'s binder records, each parting the conclusion.  The
floor: at the pivot `-1` about the center `0` the deviation's cap
holds at radius one (the lower split the kernel's) while the floor
refuses at its own split and the pivot's split reads one reversal.
The cap: at the pivot `-1` about the center `4` the floor holds
(the main battery's) while the deviation `-5` refuses the radius
and the conclusion parts at the one reversal. -/

example : capQ (devQ (([[⟨1, 2⟩]], 1) : greenprod.MatQ)
    (([[⟨1, 1⟩]], 1) : greenprod.MatQ)) [[⟨2, 1⟩]] 1 1
    (spOne ⟨3, 1⟩) spK := by decide +kernel
example : ¬ floorRead (([[⟨1, 1⟩]], 1) : greenprod.MatQ) [[⟨2, 1⟩]]
    3 1 1 1 (spOne ⟨5, 9⟩) := by decide +kernel
example : ¬ capQ (devQ (([[⟨1, 2⟩]], 1) : greenprod.MatQ)
    (([[⟨5, 1⟩]], 1) : greenprod.MatQ)) [[⟨2, 1⟩]] 1 1
    (spOne ⟨9, 3⟩) (spOne ⟨4, 8⟩) := by decide +kernel
example : ¬ psdAt (spOne ⟨1, 2⟩) := by decide +kernel

example : capWalk [[[⟨2, 1⟩]], [[⟨2, 1⟩]]] 1 1 ([[⟨3, 1⟩]], 1)
    ([[⟨4, 1⟩]], 1)
    [([[⟨2, 1⟩]], 3)] [([[⟨2, 1⟩]], 2)] [([[⟨9, 1⟩]], 3)]
    [([[⟨6, 1⟩]], 2)]
    [⟨(1, 1), (1, 3), (1, 2), spK, spK, sp2p, spK, spU', spL'⟩] := by
  decide +kernel
example : ¬ capWalk [[[⟨2, 1⟩]], [[⟨2, 1⟩]]] 1 1 ([[⟨3, 1⟩]], 1)
    ([[⟨4, 1⟩]], 1)
    [([[⟨2, 1⟩]], 3)] [([[⟨2, 1⟩]], 2)] [([[⟨9, 1⟩]], 3)]
    [([[⟨6, 1⟩]], 2)] [] := by decide +kernel

/-! The tied slab order at two windows: the committed family
`tridiag(3,3,3; 1,1)` beside `tridiag(4,4,5; 1,1)` at the drift
`δ = 1`, the tie `A'_i = A_i + 1` holding below the perturbation
slab `w0 = 2` with the couplings equal there and the window's own
datum beyond it.  The second window's tail pivots read
`X' = (71/19, 19/5, 5)` at the witnesses `R' = (5/19, 1/5)`, and
the tail deviation `E = (169/152, 17/15, 2)` obeys the tied step
`E_i = R_{i+1} E_{i+1} R'_{i+1} + 1` down the slab order.  The tie
datum's identity is capped at each step's own slab block, the
certificates carrying the two tie splits, and the walk runs its
two certified steps — `λ = 1/3, λ' = 1/5` at the root pair and
`λ = 3/8, λ' = 5/19` above it — from the seed pair `2` to the
folded pair `23305382/20793600`, the depth-`0` deviation `169/152`
inside it by the theorem route. -/

private def dnD : BPair := ⟨2, 1⟩
private def gW : Mat := [[⟨2, 1⟩]]
private def diagW : List Mat := [[[⟨5, 1⟩]], [[⟨5, 1⟩]], [[⟨6, 1⟩]]]
private def xsW : List MatQ :=
  [([[⟨72, 1⟩]], 19), ([[⟨20, 1⟩]], 5), ([[⟨6, 1⟩]], 1)]
private def rsW : List MatQ := [([[⟨6, 1⟩]], 19), ([[⟨2, 1⟩]], 5)]
private def certD : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
    × Split p.2 × Split p.2 × Split p.1 × Split p.1
    × Split p.2 × Split p.2 × Split p.2 × Split p.2) :=
  [⟨(1, 1), (1, 3), (1, 5), spK, spK, spK, spOne ⟨5, 1⟩,
      spOne ⟨121, 1⟩, spOne ⟨15421, 1⟩, spK, sp2p⟩,
   ⟨(1, 1), (3, 8), (5, 19), spK, spK, spOne ⟨121, 1⟩,
      spOne ⟨15421, 1⟩, spOne ⟨28299665, 1⟩,
      spOne ⟨7056536465, 1⟩, spK, sp2p⟩]

example : driftStep dnD ([[⟨4, 1⟩]], 8) ([[⟨6, 1⟩]], 19)
    ([[⟨72, 1⟩]], 19) ([[⟨22, 1⟩]], 8) ([[⟨20, 1⟩]], 5)
    ([[⟨9, 1⟩]], 3) 1 1 := by decide +kernel
example : driftShareRead diag3 off3 diagW off3 xs3 rs3 xsW rsW
    2 0 [1, 1, 1] dnD 2 1 1 1 [gW, gW, gW] certD := by decide +kernel
example : driftFold 2 1 1 1 certD = (23305382, 20793600) := by
  decide +kernel

/-! The bundle's walk at the depth of the observable: the tied
walk's fold-out reads the root deviation `169/152` inside the
folded pair. -/

example : ∃ (k : Nat) (spU spL : Split k),
    capQ (devQ (ground.getAt dM xsW 0) (ground.getAt dM xs3 0)) gW
      (driftFold 2 1 1 1 certD).1 (driftFold 2 1 1 1 certD).2
      spU spL :=
  driftShare_cap diag3 off3 diagW off3 xs3 rs3 xsW rsW 2 0 [1, 1, 1]
    dnD 2 1 1 1 [gW, gW, gW] certD (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The tied bundle's binder records, each parting the read.  The
diagonal tie: the second window's root diagonal raised one past the
drift parts the tie at that slab.  The tied step: the root pivot
forged at `72/19` parts the step's identity.  The seed pair: the
root deviation at two against a seed cap of one parts the walk's
first tied step.  The depth binder: at `j = w0` the walk's lists
are vacant and name no cap.  The step's tie cap: the first step's
lower tie split narrowed to the kernel's parts the walk at that
step's read, and at the narrowed pair `1/2` the tie datum's
identity leaves the upper site datum at one reversal, the split
reading the datum and the reversal count refusing. -/

private def certDF : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
    × Split p.2 × Split p.2 × Split p.1 × Split p.1
    × Split p.2 × Split p.2 × Split p.2 × Split p.2) :=
  [⟨(1, 1), (1, 3), (1, 5), spK, spK, spK, spOne ⟨5, 1⟩,
      spOne ⟨121, 1⟩, spOne ⟨15421, 1⟩, spK, spK⟩,
   ⟨(1, 1), (3, 8), (5, 19), spK, spK, spOne ⟨121, 1⟩,
      spOne ⟨15421, 1⟩, spOne ⟨28299665, 1⟩,
      spOne ⟨7056536465, 1⟩, spK, sp2p⟩]

example : ¬ driftShareRead diag3 off3
    [[[⟨6, 1⟩]], [[⟨5, 1⟩]], [[⟨6, 1⟩]]] off3 xs3 rs3 xsW rsW
    2 0 [1, 1, 1] dnD 2 1 1 1 [gW, gW, gW] certD := by decide +kernel
example : ¬ driftStep dnD ([[⟨4, 1⟩]], 8) ([[⟨6, 1⟩]], 19)
    ([[⟨73, 1⟩]], 19) ([[⟨22, 1⟩]], 8) ([[⟨20, 1⟩]], 5)
    ([[⟨9, 1⟩]], 3) 1 1 := by decide +kernel
example : ¬ driftShareRead diag3 off3 diagW off3 xs3 rs3 xsW rsW
    2 0 [1, 1, 1] dnD 1 1 1 1 [gW, gW, gW] certD := by decide +kernel
example : ¬ (2 < 2) := by decide +kernel
example : ¬ driftShareRead diag3 off3 diagW off3 xs3 rs3 xsW rsW
    2 0 [1, 1, 1] dnD 2 1 1 1 [gW, gW, gW] certDF := by decide +kernel
example : splitRead (siteDatum (matScale (1 * Pos.one) gW)
    (matScale 2 (matScaleB dnD (idMat 1)))) (spOne ⟨1, 2⟩) := by
  decide +kernel
example : ¬ capQ ((matScaleB dnD (idMat 1)), Pos.one) gW 1 2
    (spOne ⟨1, 2⟩) (spOne ⟨4, 1⟩) := by decide +kernel

/-! The tie's equal-membered case: at the drift the sum's unit the
bundle reads the committed reversed pair `tridiag(3,3,3; 1,1)`
beside `tridiag(3,3,4; 1,1)`, the tail deviation
`E = (1/88, 1/12, 1)` walked from the seed pair one to the folded
pair `5121913/2230272` at the certificates `λ = 1/3, λ' = 1/4` and
`λ = 3/8, λ' = 4/11`. -/

private def certV : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
    × Split p.2 × Split p.2 × Split p.1 × Split p.1
    × Split p.2 × Split p.2 × Split p.2 × Split p.2) :=
  [⟨(1, 1), (1, 3), (1, 4), spK, spK, spK, sp2p,
      spOne ⟨3469, 1⟩, spOne ⟨4045, 1⟩, spOne ⟨2, 1⟩,
      spOne ⟨2, 1⟩⟩,
   ⟨(1, 1), (3, 8), (4, 11), spK, spK, spOne ⟨3469, 1⟩,
      spOne ⟨4045, 1⟩, spOne ⟨446267801, 1⟩,
      spOne ⟨455188889, 1⟩, spOne ⟨2, 1⟩, spOne ⟨2, 1⟩⟩]

example : driftShareRead diag3 off3 diagV off3 xs3 rs3 xsV rsV
    2 0 [1, 1, 1] BPair.unit 1 1 1 1 [gW, gW, gW]
    certV := by decide +kernel

/-! The tied walk at a gap of varying orders: `ns = [1, 2, 1]`
with the perturbation slab `w0 = 2` and the observable at the
root, the earlier family `tridiag(3, diag(3, 2), 2; [1 1], [2 0]ᵀ)`
at the pivots `(3/2, diag(1, 2), 2)` beside the tied
`tridiag(4, diag(4, 3), 4)` at `(10/3, diag(3, 3), 4)`, the drift
`δ = 1` below the slab and the window's own datum beyond.  The
walk's two steps cross the orders — the deep factor `[1 0]`
against `[1 0]/2`, the root factor `[2 1]ᵀ/2` against `[1 1]ᵀ/3`
at the certificates `[2 : 1]` and `[1 : 1]` — from the seed pair
`2` to the folded pair `[34 : 4]`, each step's tie datum capped at
its own slab's identity. -/

private def diagG : List Mat :=
  [[[⟨4, 1⟩]], [[⟨4, 1⟩, u], [u, ⟨3, 1⟩]], [[⟨3, 1⟩]]]
private def offG : List Mat := [[[⟨2, 1⟩, ⟨2, 1⟩]], [[⟨3, 1⟩], [u]]]
private def xsG : List MatQ :=
  [([[⟨4, 1⟩]], 2), ([[⟨2, 1⟩, u], [u, ⟨3, 1⟩]], 1), ([[⟨3, 1⟩]], 1)]
private def rsG : List MatQ :=
  [([[⟨3, 1⟩], [⟨2, 1⟩]], 2), ([[⟨2, 1⟩, u]], 1)]
private def diagG' : List Mat :=
  [[[⟨5, 1⟩]], [[⟨5, 1⟩, u], [u, ⟨4, 1⟩]], [[⟨5, 1⟩]]]
private def xsG' : List MatQ :=
  [([[⟨11, 1⟩]], 3), ([[⟨4, 1⟩, u], [u, ⟨4, 1⟩]], 1), ([[⟨5, 1⟩]], 1)]
private def rsG' : List MatQ :=
  [([[⟨2, 1⟩], [⟨2, 1⟩]], 3), ([[⟨2, 1⟩, u]], 2)]

private def spZ2 : Split 2 := mkSplit 2 [[u, u], [u, u]]
private def sp2I : Split 2 := mkSplit 2 [[⟨3, 1⟩, u], [u, ⟨3, 1⟩]]
private def spD01 : Split 2 := mkSplit 2 [[u, u], [u, ⟨2, 1⟩]]
private def spD34 : Split 2 := mkSplit 2 [[⟨4, 1⟩, u], [u, ⟨5, 1⟩]]
private def spD24 : Split 2 := mkSplit 2 [[⟨3, 1⟩, u], [u, ⟨5, 1⟩]]
private def spD108 : Split 2 := mkSplit 2 [[⟨11, 1⟩, u], [u, ⟨9, 1⟩]]

private def certG : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
    × Split p.2 × Split p.2 × Split p.1 × Split p.1
    × Split p.2 × Split p.2 × Split p.2 × Split p.2) :=
  [⟨(1, 2), (1, 1), (1, 1), spD01, spD34, spK, spOne ⟨5, 1⟩,
      spD24, spD108, spZ2, sp2I⟩,
   ⟨(2, 1), (2, 1), (1, 1), spOne ⟨12, 1⟩, spOne ⟨8, 1⟩,
      spD24, spD108, spOne ⟨161, 1⟩, spOne ⟨249, 1⟩, spK, sp2p⟩]

example : tailRead diagG offG xsG rsG [1, 2, 1] := by decide +kernel
example : tailRead diagG' offG xsG' rsG' [1, 2, 1] := by decide +kernel
example : driftShareRead diagG offG diagG' offG xsG rsG xsG' rsG'
    2 0 [1, 2, 1] dnD 2 1 1 1 [idMat 1, idMat 2, idMat 1]
    certG := by decide +kernel
example : driftFold 2 1 1 1 certG = (34, 4) := by decide +kernel
example : ∃ (k : Nat) (spU spL : Split k),
    capQ (devQ (ground.getAt dM xsG' 0) (ground.getAt dM xsG 0))
      (idMat 1) (driftFold 2 1 1 1 certG).1
      (driftFold 2 1 1 1 certG).2 spU spL :=
  driftShare_cap diagG offG diagG' offG xsG rsG xsG' rsG' 2 0
    [1, 2, 1] dnD 2 1 1 1 [idMat 1, idMat 2, idMat 1] certG
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The refusal isolating the gram list's own orders: at the unit
gram of the wrong order at the middle slab the deep step's
contraction certificate parts at its image gram's shape. -/
example : ¬ driftShareRead diagG offG diagG' offG xsG rsG xsG' rsG'
    2 0 [1, 2, 1] dnD 2 1 1 1 [idMat 1, idMat 1, idMat 1]
    certG := by decide +kernel

/-- The refusal isolating the certificate's own arithmetic: the
root factor's pair forged at `[3 : 1]` against its committed site
datum. -/
private def certGF : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
    × Split p.2 × Split p.2 × Split p.1 × Split p.1
    × Split p.2 × Split p.2 × Split p.2 × Split p.2) :=
  [⟨(1, 2), (1, 1), (1, 1), spD01, spD34, spK, spOne ⟨5, 1⟩,
      spD24, spD108, spZ2, sp2I⟩,
   ⟨(2, 1), (3, 1), (1, 1), spOne ⟨12, 1⟩, spOne ⟨8, 1⟩,
      spD24, spD108, spOne ⟨161, 1⟩, spOne ⟨249, 1⟩, spK, sp2p⟩]

example : ¬ driftShareRead diagG offG diagG' offG xsG rsG xsG' rsG'
    2 0 [1, 2, 1] dnD 2 1 1 1 [idMat 1, idMat 2, idMat 1]
    certGF := by decide +kernel

/-- The refusal isolating the step's own tie cap at the varying
gap: the deep step's upper tie split forged at the doubled
identity's parts the walk at that step's read. -/
private def certGT : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
    × Split p.2 × Split p.2 × Split p.1 × Split p.1
    × Split p.2 × Split p.2 × Split p.2 × Split p.2) :=
  [⟨(1, 2), (1, 1), (1, 1), spD01, spD34, spK, spOne ⟨5, 1⟩,
      spD24, spD108, sp2I, sp2I⟩,
   ⟨(2, 1), (2, 1), (1, 1), spOne ⟨12, 1⟩, spOne ⟨8, 1⟩,
      spD24, spD108, spOne ⟨161, 1⟩, spOne ⟨249, 1⟩, spK, sp2p⟩]

example : ¬ driftShareRead diagG offG diagG' offG xsG rsG xsG' rsG'
    2 0 [1, 2, 1] dnD 2 1 1 1 [idMat 1, idMat 2, idMat 1]
    certGT := by decide +kernel

/-! The same gap at the observable one slab up: `j = 1` leaves the
non-palindromic orders `[1, 2]` on the walk, the one step from the
seed pair `2` to `[6 : 2]`, the block list read deep-first with the
reversed list refused, and the fold-out's cap landing at the middle
slab's own two-dimensional block. -/

private def certG1 : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
    × Split p.2 × Split p.2 × Split p.1 × Split p.1
    × Split p.2 × Split p.2 × Split p.2 × Split p.2) :=
  [⟨(1, 2), (1, 1), (1, 1), spD01, spD34, spK, spOne ⟨5, 1⟩,
      spD24, spD108, spZ2, sp2I⟩]

example : driftShareRead diagG offG diagG' offG xsG rsG xsG' rsG'
    2 1 [1, 2, 1] dnD 2 1 1 1 [idMat 1, idMat 2] certG1 := by
  decide +kernel
example : driftFold 2 1 1 1 certG1 = (6, 2) := by decide +kernel
example : ∃ (k : Nat) (spU spL : Split k),
    capQ (devQ (ground.getAt dM xsG' 1) (ground.getAt dM xsG 1))
      (idMat 2) (driftFold 2 1 1 1 certG1).1
      (driftFold 2 1 1 1 certG1).2 spU spL :=
  driftShare_cap diagG offG diagG' offG xsG rsG xsG' rsG' 2 1
    [1, 2, 1] dnD 2 1 1 1 [idMat 1, idMat 2] certG1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The refusal isolating the block list's orientation: the walk
reads its blocks deep-first, the reversed list parting the deep
step's contraction certificate at its image block's shape. -/
example : ¬ driftShareRead diagG offG diagG' offG xsG rsG xsG' rsG'
    2 1 [1, 2, 1] dnD 2 1 1 1 [idMat 2, idMat 1] certG1 := by
  decide +kernel

/-! The untied step at two blocks: clause (ii)'s cap step crossing
the orders one to two, the factor `[1 0]` at the unit certificates,
the deviation `3` capped at the deeper block and the doubled next
`diag(6, 0)` at the headward — the blocks exchanged refused at the
image block's shape. -/

private def spD06 : Split 2 := mkSplit 2 [[u, u], [u, ⟨7, 1⟩]]
private def spD126 : Split 2 := mkSplit 2 [[⟨13, 1⟩, u], [u, ⟨7, 1⟩]]

example : capStepRead ([[⟨2, 1⟩, u]], 1) ([[⟨2, 1⟩, u]], 1)
    ([[⟨4, 1⟩, u], [u, u]], 1) ([[u, u], [u, u]], 1)
    ([[⟨4, 1⟩]], 1) ([[u]], 1) (idMat 1) (idMat 2) 3 1 1 1 1 1
    spD01 spD01 spK (spOne ⟨7, 1⟩) spD06 spD126 := by decide +kernel
example : ¬ capStepRead ([[⟨2, 1⟩, u]], 1) ([[⟨2, 1⟩, u]], 1)
    ([[⟨4, 1⟩, u], [u, u]], 1) ([[u, u], [u, u]], 1)
    ([[⟨4, 1⟩]], 1) ([[u]], 1) (idMat 2) (idMat 1) 3 1 1 1 1 1
    spD01 spD01 spK (spOne ⟨7, 1⟩) spD06 spD126 := by decide +kernel
