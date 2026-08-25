import MassGap.Spectator
/-!
The check module for `lem:spectator`: the batteries re-read the
spectator law by kernel `decide` at the two scalar three-slab
families `tridiag(3,3,3; 1,1)` and `tridiag(2,3,3; 1,1)`, the
perturbation at the first slab.  Clause (i): the tail pivots equal
beyond the perturbation (`X = (21/8, 8/3, 3)` against
`(13/8, 8/3, 3)`), and the deviation sandwich telescoping exactly,
`D = (-1, -1/6, -1/40)` at the transfer factors, with the
forged-deviation refusal.  Clause (ii): the cap step at the
contraction certificates `λ = 1/3`, `λ' = 1/2` — the deviation
capped at `G` and the doubled next deviation at `13/36 · G`.
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
vacant certificate list. -/
set_option maxRecDepth 8192
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

/-! Clause (ii): the cap step at the contraction certificates. -/

private def spK : Split 1 := ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [], 1, rfl⟩
private def spOne (a : BPair) : Split 1 :=
  ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one a], 0, rfl⟩
private def sp2p : Split 1 := spOne ⟨3, 1⟩
private def spU' : Split 1 := spOne ⟨151, 1⟩
private def spL' : Split 1 := spOne ⟨7, 1⟩

example : contractRead (transfer ([[⟨2, 1⟩]], 3)) [[⟨2, 1⟩]] 1 3
    spK := by decide +kernel
example : capQ (devQ ([[⟨3, 1⟩]], 1) ([[⟨4, 1⟩]], 1)) [[⟨2, 1⟩]]
    1 1 sp2p spK := by decide +kernel
example : capStepRead ([[⟨2, 1⟩]], 3) ([[⟨2, 1⟩]], 2)
    ([[⟨6, 1⟩]], 2) ([[⟨9, 1⟩]], 3) ([[⟨3, 1⟩]], 1) ([[⟨4, 1⟩]], 1)
    [[⟨2, 1⟩]] 1 1 1 3 1 2 spK spK sp2p spK spU' spL' := by decide +kernel

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

example : capWalk [[⟨2, 1⟩]] 1 1 ([[⟨3, 1⟩]], 1) ([[⟨4, 1⟩]], 1)
    [([[⟨2, 1⟩]], 3)] [([[⟨2, 1⟩]], 2)] [([[⟨9, 1⟩]], 3)]
    [([[⟨6, 1⟩]], 2)]
    [((1, 3), (1, 2), spK, spK, sp2p, spK, spU', spL')] := by decide +kernel
example : ¬ @capWalk 1 [[⟨2, 1⟩]] 1 1 ([[⟨3, 1⟩]], 1) ([[⟨4, 1⟩]], 1)
    [([[⟨2, 1⟩]], 3)] [([[⟨2, 1⟩]], 2)] [([[⟨9, 1⟩]], 3)]
    [([[⟨6, 1⟩]], 2)] [] := by decide +kernel
