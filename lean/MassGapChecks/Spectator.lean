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
parting at the head-perturbed pair.  The derived sandwich
(`sandwich_of_steps`) re-reads the committed step at the theorem
route, the binder records parting the conclusion at the two moved
centers, the two moved pivots, and the asymmetric `Y0` of the
two-by-two fixture.  Clause (ii): the cap step at the
contraction certificates `λ = 1/3`, `λ' = 1/2` — the deviation
capped at the deeper slab's block and the doubled next deviation at
`13/36` of the step's own — beside the step at two blocks of
crossing orders; the derived price (`cap_step_price`) prices the
read's conclusion from its leading conjuncts, the theorem route on
both sides beside the decided reads with the collected weight's
margin refused at eleven, one record per conjunct — the moved
pivot, the two starved moduli, the tightened cap — each beside its
parted side, and the bridge records at the starved modulus
(`contract_all`), the tightened cap (`cap_lo`), and the positive
deviation (`cap_hi`).
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
the theorem route at the stated splits, with the member's floor
(`ball_floor`) pricing it at or beyond three times the gram and
the two floored-read partings the binder records' own; and one cap step walked
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
orders and at the root factor's forged pair.
The derived ball and transport tier closes the module at the tight
center `Ŷ = 4`, the member `Y = 1` at the floor `y0 = 1` and the
radius `ρ = 3`: the deviation's form expansion at the cleared
difference; the deviation's triangle at the two caps'
cross-collected weight — `5, 3, 2` at the caps `2` and `1`, the
conclusion at three against three exactly — with the two starved
partings, the leading cap starved at one parting the upper side at
three against two and the trailing cap's modulus doubled parting it
at six against five; clause (ii)'s polarization at the promoted
cross read — the cross datum `-1` capped at the unit gram, the two
conjuncts at minus four and four against five — with the
antisymmetric two-by-two record parting the conclusion at two
thousand against two, the caps standing at that datum, its
quadratic form unit-valued at every vector; clause (iii)'s pricing
at the tight center with the member's transfer factor priced at
sixteen against sixteen exactly, and the five isolating refusals —
the forged floor at `y0 = 2` parting at sixty-four against
twenty-five, the starved cap at `ρ = 1` parting at sixteen against
four, the starved contraction at `λ = 1/5` parting at twenty-five
against sixteen, the forged member witness parting at sixty-four
against sixteen, and the bond forged at ten parting at sixteen
hundred against sixteen; and clause (iii)'s image deviation at the
same family — the deeper image `3` about the middle center `15/4`
at the modulus `λ∘ = 1` — with the tie's refusal parting the swap
side at minus twelve against minus forty-eight.  The member's
symmetry binder is load-bearing, the record at two orders: the
unbalanced center `diag(100, 2)` at the radius `[1 : 1000]` with
the member the center joined to the antisymmetric bond deviation
`E₁₂ - E₂₁` — the deviation's form
unit-valued at every vector, so both caps and the floor hold at
the tiny radius while the member's transfer factor and image blow
past the modulus, the refused transpose read beside the two parted
conclusions with every co-binder standing.  The center's symmetry
binder is `lem:spectator`(iii)'s stated datum, the located
symmetric `Ŷ`; the gram's, kept at `transfer_price` alone, is the
pairing's own (`def:carrier`), the image tier deriving it off the
floor's split.  The pivot's upper-side read at the transported
ball (`ball_psd_of`) closes the module: the pass at the
equal-membered pair `Y = Ŷ = 3` about the unit gram at the floor
`y0 = 1` and radius one, the vacant deviation leaving both cap
matrices the gram, decided raw and through the theorem at the
caps' pointwise form; and the upper cap's binder load-bearing at
the indefinite gram `diag(1, -1)` of order two — the center
`[[4,1],[1,-2]]` and member `[[2,1],[1,0]]` at the clearing two,
the deviation `diag(-4, 4)` making the lower side an exact
equality at every vector while the upper side refuses at `(-1, 2)`
at twelve against minus twelve, the center's floor and the
member's split standing and the conclusion parting at the
indefinite block's one reversal; the lower cap side parts at the
member `-1` below the center `3`, the deviation the gram's swap at
the quadruple scale with the upper side held at every vector; and
the floor parts at the member at its own center `-1`, the vacant
deviation holding both cap sides. -/
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

/-! Clause (i)'s sandwich, derived: the theorem route at the two
families' slab `0 → 1` step data beside the decided read.  The
binder records: the moved centers refuse one witness each and the
conclusion parts — the unprimed at `4`, the primed at `3`, the
latter withdrawing the deviation against the surviving `-1/6`;
the moved pivots refuse one join each and the conclusion parts
beside them — the unprimed at `3`, the primed reading the
deviation `1/3`; and the symmetry record at the two-by-two
fixture — the asymmetric `Y0` with every further read holding,
the conclusion parting — the one load-bearing symmetry, the shape
binders the committed read's own frame. -/

example : oneValueQ
    (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3))
    (mulQ (transposeQ (transfer ([[⟨2, 1⟩]], 3)))
      (mulQ (devQ (([[⟨3, 1⟩]], 1) : MatQ) ([[⟨4, 1⟩]], 1))
        (transfer ([[⟨2, 1⟩]], 2)))) :=
  sandwich_of_steps (n := 1) (n' := 1) ([[⟨2, 1⟩]], 3)
    ([[⟨2, 1⟩]], 2) ([[⟨6, 1⟩]], 2) ([[⟨9, 1⟩]], 3)
    ([[⟨3, 1⟩]], 1) ([[⟨4, 1⟩]], 1) [[⟨4, 1⟩]] [[⟨2, 1⟩]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
example : oneValueQ
    (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3))
    (mulQ (transposeQ (transfer ([[⟨2, 1⟩]], 3)))
      (mulQ (devQ (([[⟨3, 1⟩]], 1) : MatQ) ([[⟨4, 1⟩]], 1))
        (transfer ([[⟨2, 1⟩]], 2)))) := by decide +kernel
example : ¬ oneValueQ
    (mulQ (([[⟨5, 1⟩]], 1) : MatQ) ([[⟨2, 1⟩]], 3))
    (ofM [[⟨2, 1⟩]]) := by decide +kernel
example : ¬ oneValueQ
    (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3))
    (mulQ (transposeQ (transfer ([[⟨2, 1⟩]], 3)))
      (mulQ (devQ (([[⟨3, 1⟩]], 1) : MatQ) ([[⟨5, 1⟩]], 1))
        (transfer ([[⟨2, 1⟩]], 2)))) := by decide +kernel
example : ¬ oneValueQ (mulQ (([[⟨4, 1⟩]], 1) : MatQ) ([[⟨2, 1⟩]], 2))
    (ofM [[⟨2, 1⟩]]) := by decide +kernel
example : ¬ oneValueQ
    (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3))
    (mulQ (transposeQ (transfer ([[⟨2, 1⟩]], 3)))
      (mulQ (devQ (([[⟨4, 1⟩]], 1) : MatQ) ([[⟨4, 1⟩]], 1))
        (transfer ([[⟨2, 1⟩]], 2)))) := by decide +kernel
example : ¬ oneValueQ
    (addQ (([[⟨10, 1⟩]], 3) : MatQ)
      (mulQ (ofM (transposeM [[⟨2, 1⟩]])) ([[⟨2, 1⟩]], 3)))
    (ofM [[⟨4, 1⟩]]) := by decide +kernel
example : ¬ oneValueQ
    (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨10, 1⟩]], 3))
    (mulQ (transposeQ (transfer ([[⟨2, 1⟩]], 3)))
      (mulQ (devQ (([[⟨3, 1⟩]], 1) : MatQ) ([[⟨4, 1⟩]], 1))
        (transfer ([[⟨2, 1⟩]], 2)))) := by decide +kernel
example : ¬ oneValueQ
    (addQ (([[⟨4, 1⟩]], 1) : MatQ)
      (mulQ (ofM (transposeM [[⟨2, 1⟩]])) ([[⟨2, 1⟩]], 2)))
    (ofM [[⟨4, 1⟩]]) := by decide +kernel
example : ¬ oneValueQ
    (devQ (([[⟨4, 1⟩]], 1) : MatQ) ([[⟨9, 1⟩]], 3))
    (mulQ (transposeQ (transfer ([[⟨2, 1⟩]], 3)))
      (mulQ (devQ (([[⟨3, 1⟩]], 1) : MatQ) ([[⟨4, 1⟩]], 1))
        (transfer ([[⟨2, 1⟩]], 2)))) := by decide +kernel

/-! The symmetry record's two-by-two fixture: `Y0 = [[2,1],[0,2]]`
asymmetric, `C` the identity, `B = Y0`, `Y0' = [[3,1],[1,3]]`
symmetric with its solved `C'` at the clearing eight,
`A = [[5,2],[2,5]]`, and the two joins' pivots computed — every
listed read decided true beside the refused symmetry and the
parted conclusion. -/

private def y0A : Mat := [[⟨3, 1⟩, ⟨2, 1⟩], [⟨1, 1⟩, ⟨3, 1⟩]]
private def cIf : Mat := [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]
private def y0S : Mat := [[⟨4, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨4, 1⟩]]
private def cPf : Mat := [[⟨7, 1⟩, ⟨2, 1⟩], [⟨1, 3⟩, ⟨6, 1⟩]]
private def aSf : Mat := [[⟨6, 1⟩, ⟨3, 1⟩], [⟨3, 1⟩, ⟨6, 1⟩]]
private def y1A : Mat := [[⟨4, 1⟩, ⟨3, 1⟩], [⟨2, 1⟩, ⟨4, 1⟩]]
private def y1P : Mat := [[⟨29, 1⟩, ⟨15, 1⟩], [⟨15, 1⟩, ⟨30, 1⟩]]

example : oneValueQ (mulQ ((y0A, 1) : MatQ) ((cIf, 1) : MatQ))
    (ofM y0A) := by decide +kernel
example : oneValueQ (mulQ ((y0S, 1) : MatQ) ((cPf, 8) : MatQ))
    (ofM y0A) := by decide +kernel
example : oneValueQ
    (addQ ((y1A, 1) : MatQ)
      (mulQ (ofM (transposeM y0A)) ((cIf, 1) : MatQ)))
    (ofM aSf) := by decide +kernel
example : oneValueQ
    (addQ ((y1P, 8) : MatQ)
      (mulQ (ofM (transposeM y0A)) ((cPf, 8) : MatQ)))
    (ofM aSf) := by decide +kernel
example : ¬ matOneValue (transposeM y0A) y0A := by decide +kernel
example : ¬ oneValueQ (devQ ((y1P, 8) : MatQ) ((y1A, 1) : MatQ))
    (mulQ (transposeQ (transfer ((cIf, 1) : MatQ)))
      (mulQ (devQ ((y0S, 1) : MatQ) ((y0A, 1) : MatQ))
        (transfer ((cPf, 8) : MatQ)))) := by decide +kernel

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

/-! Clause (ii)'s step, derived: the theorem prices the doubled
deviation two-sidedly at the committed step read's own collected
weights from the read's leading conjuncts — the step, the two
contraction certificates (the primed factor's beside the
unprimed's), and the deviation's cap — the theorem route on both
sides beside the decided reads, with the collected weight's margin
refused at eleven against the collected thirteen. -/

example : contractRead (transfer ([[⟨2, 1⟩]], 2)) [[⟨2, 1⟩]]
    [[⟨2, 1⟩]] 1 2 spK := by decide +kernel
example : (quadForm
      (matScale 2
        (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).1)
      [⟨2, 1⟩]).scale (1 * (3 * 3 * (2 * 2)))
    ≤ (quadForm [[⟨2, 1⟩]] [⟨2, 1⟩]).scale
      (1 * (1 * 1 * (2 * 2) + 1 * 1 * (3 * 3))
        * (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).2) :=
  (cap_step_price (n := 1) (n' := 1) ([[⟨2, 1⟩]], 3)
    ([[⟨2, 1⟩]], 2) ([[⟨6, 1⟩]], 2) ([[⟨9, 1⟩]], 3)
    ([[⟨3, 1⟩]], 1) ([[⟨4, 1⟩]], 1) [[⟨2, 1⟩]] [[⟨2, 1⟩]]
    1 1 1 3 1 2 spK spK sp2p spK
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).1 [⟨2, 1⟩] rfl
example : (quadForm
      (matScale 2
        (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).1)
      [⟨2, 1⟩]).scale (1 * (3 * 3 * (2 * 2)))
    ≤ (quadForm [[⟨2, 1⟩]] [⟨2, 1⟩]).scale
      (1 * (1 * 1 * (2 * 2) + 1 * 1 * (3 * 3))
        * (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).2) := by
  decide +kernel
example : ((quadForm [[⟨2, 1⟩]] [⟨2, 1⟩]).scale
      (1 * (1 * 1 * (2 * 2) + 1 * 1 * (3 * 3))
        * (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).2)).swap
    ≤ (quadForm
      (matScale 2
        (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).1)
      [⟨2, 1⟩]).scale (1 * (3 * 3 * (2 * 2))) :=
  (cap_step_price (n := 1) (n' := 1) ([[⟨2, 1⟩]], 3)
    ([[⟨2, 1⟩]], 2) ([[⟨6, 1⟩]], 2) ([[⟨9, 1⟩]], 3)
    ([[⟨3, 1⟩]], 1) ([[⟨4, 1⟩]], 1) [[⟨2, 1⟩]] [[⟨2, 1⟩]]
    1 1 1 3 1 2 spK spK sp2p spK
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).2 [⟨2, 1⟩] rfl
example : ((quadForm [[⟨2, 1⟩]] [⟨2, 1⟩]).scale
      (1 * (1 * 1 * (2 * 2) + 1 * 1 * (3 * 3))
        * (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).2)).swap
    ≤ (quadForm
      (matScale 2
        (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).1)
      [⟨2, 1⟩]).scale (1 * (3 * 3 * (2 * 2))) := by decide +kernel
example : ¬ (((quadForm [[⟨2, 1⟩]] [⟨2, 1⟩]).scale
      (11 * (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).2)).swap
    ≤ (quadForm
      (matScale 2
        (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).1)
      [⟨2, 1⟩]).scale (1 * (3 * 3 * (2 * 2)))) := by decide +kernel

/-! The step theorem's binder records, one per leading conjunct,
each refusal beside the parted conclusion at its own constants:
the moved pivot parts the step read and the upper side, the two
starved moduli part their contraction reads and the swap side,
and the tightened cap parts the cap read and the swap side.  The
bridge records beneath them: the starved modulus parts
`contract_all`'s vector read, the tightened cap parts `cap_lo`'s
lower read, and the positive deviation at the tightened cap parts
`cap_hi`'s upper read. -/

example : ¬ ((quadForm
      (matScale 2
        (devQ (([[⟨7, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).1)
      [⟨2, 1⟩]).scale (1 * (3 * 3 * (2 * 2)))
    ≤ (quadForm [[⟨2, 1⟩]] [⟨2, 1⟩]).scale
      (1 * (1 * 1 * (2 * 2) + 1 * 1 * (3 * 3))
        * (devQ (([[⟨7, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).2)) := by
  decide +kernel
example : ¬ contractRead (transfer ([[⟨2, 1⟩]], 3)) [[⟨2, 1⟩]]
    [[⟨2, 1⟩]] 1 4 spK := by decide +kernel
example : ¬ (((quadForm [[⟨2, 1⟩]] [⟨2, 1⟩]).scale
      (1 * (1 * 1 * (2 * 2) + 1 * 1 * (4 * 4))
        * (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).2)).swap
    ≤ (quadForm
      (matScale 2
        (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).1)
      [⟨2, 1⟩]).scale (1 * (4 * 4 * (2 * 2)))) := by decide +kernel
example : ¬ contractRead (transfer ([[⟨2, 1⟩]], 2)) [[⟨2, 1⟩]]
    [[⟨2, 1⟩]] 1 3 spK := by decide +kernel
example : ¬ (((quadForm [[⟨2, 1⟩]] [⟨2, 1⟩]).scale
      (1 * (1 * 1 * (3 * 3) + 1 * 1 * (3 * 3))
        * (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).2)).swap
    ≤ (quadForm
      (matScale 2
        (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).1)
      [⟨2, 1⟩]).scale (1 * (3 * 3 * (3 * 3)))) := by decide +kernel
example : ¬ capQ (devQ (([[⟨3, 1⟩]], 1) : MatQ) ([[⟨4, 1⟩]], 1))
    [[⟨2, 1⟩]] 1 2 sp2p spK := by decide +kernel
example : ¬ (((quadForm [[⟨2, 1⟩]] [⟨2, 1⟩]).scale
      (1 * (1 * 1 * (2 * 2) + 1 * 1 * (3 * 3))
        * (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).2)).swap
    ≤ (quadForm
      (matScale 2
        (devQ (([[⟨6, 1⟩]], 2) : MatQ) ([[⟨9, 1⟩]], 3)).1)
      [⟨2, 1⟩]).scale (2 * (3 * 3 * (2 * 2)))) := by decide +kernel
example : ¬ ((quadForm [[⟨2, 1⟩]]
      (matVec [[⟨1, 2⟩]] [⟨2, 1⟩])).scale (4 * 4)
    ≤ (quadForm [[⟨2, 1⟩]] [⟨2, 1⟩]).scale (1 * 1 * (3 * 3))) := by
  decide +kernel
example : ¬ (((quadForm [[⟨2, 1⟩]] [⟨2, 1⟩]).scale
      (1 * (devQ (([[⟨3, 1⟩]], 1) : MatQ) ([[⟨4, 1⟩]], 1)).2)).swap
    ≤ (quadForm
      (devQ (([[⟨3, 1⟩]], 1) : MatQ) ([[⟨4, 1⟩]], 1)).1
      [⟨2, 1⟩]).scale 2) := by
  decide +kernel
example : ¬ capQ (devQ (([[⟨5, 1⟩]], 1) : MatQ) ([[⟨4, 1⟩]], 1))
    [[⟨2, 1⟩]] 1 2 sp2p spK := by decide +kernel
example : ¬ ((quadForm
      (devQ (([[⟨5, 1⟩]], 1) : MatQ) ([[⟨4, 1⟩]], 1)).1
      [⟨2, 1⟩]).scale 2
    ≤ (quadForm [[⟨2, 1⟩]] [⟨2, 1⟩]).scale
      (1 * (devQ (([[⟨5, 1⟩]], 1) : MatQ) ([[⟨4, 1⟩]], 1)).2)) := by
  decide +kernel

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

/-! The member's floor at the ball (`ball_floor`), the theorem
route beside the decided read: the center `4` at floor `y0 = 3`
and radius one prices the member `5` at or beyond three times the
gram.  The binder records, at `ball_psd`'s two record cells above:
at the member `-1` about the center `4` the floor holds while the
deviation refuses the radius, and the floored read parts; at the
member `-1` about the center `0` the deviation's cap holds while
the floor refuses, and the floored read parts beside it — one
refusal per load-bearing binder, the shape binders the consumers'
own pivot frame. -/

example : (quadForm [[⟨2, 1⟩]] [⟨2, 1⟩]).scale (3 * 1)
    ≤ (quadForm [[⟨6, 1⟩]] [⟨2, 1⟩]).scale 1 :=
  ball_floor ([[⟨6, 1⟩]], 1) ([[⟨5, 1⟩]], 1) [[⟨2, 1⟩]] 3 1 1 1
    spK spK sp2p (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) [⟨2, 1⟩] rfl
example : (quadForm [[⟨2, 1⟩]] [⟨2, 1⟩]).scale (3 * 1)
    ≤ (quadForm [[⟨6, 1⟩]] [⟨2, 1⟩]).scale 1 := by decide +kernel
example : ¬ ((quadForm [[⟨2, 1⟩]] [⟨2, 1⟩]).scale (3 * 1)
    ≤ (quadForm [[⟨1, 2⟩]] [⟨2, 1⟩]).scale 1) := by decide +kernel

/-! The member's floor at ∀-form entries throughout
(`ball_floor_ptw`), the theorem route at the same data: the center
`4` at floor `y0 = 3` and radius one prices the member `5` at or
beyond three times the gram, the floor read and the cap's lower
side entering as their pointwise transports (`floor_all` and
`cap_lo`). -/

example : (quadForm [[⟨2, 1⟩]] [⟨2, 1⟩]).scale (3 * 1)
    ≤ (quadForm [[⟨6, 1⟩]] [⟨2, 1⟩]).scale 1 :=
  ball_floor_ptw (o := 1) ([[⟨6, 1⟩]], 1) ([[⟨5, 1⟩]], 1)
    [[⟨2, 1⟩]] 3 1 1 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun w hw => floor_all ([[⟨5, 1⟩]], 1) [[⟨2, 1⟩]] 3 1 1 1 spK
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      w hw)
    (fun w hw => cap_lo (devQ ([[⟨6, 1⟩]], 1) ([[⟨5, 1⟩]], 1))
      [[⟨2, 1⟩]] 1 1 spK sp2p (by decide +kernel) w hw)
    [⟨2, 1⟩] rfl

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

/-! The derived ball and transport tier's fixture: the center
`Ŷ = 4` at the floor `y0 = 1` and radius `ρ = 3`, the member
`Y = 1` with its witness `1` and the center's witness `1/4` at the
bond `1`, the deeper image `3` about the middle center `15/4`, and
the triangle's three members `5, 3, 2` at the unit gram. -/

private def ycT : MatQ := ([[⟨5, 1⟩]], 1)
private def yT : MatQ := ([[⟨2, 1⟩]], 1)
private def btT : Mat := [[⟨2, 1⟩]]
private def ccT : MatQ := ([[⟨2, 1⟩]], 4)
private def cxT : MatQ := ([[⟨2, 1⟩]], 1)
private def xmT : MatQ := ([[⟨6, 1⟩]], 1)
private def ymT : MatQ := ([[⟨4, 1⟩]], 1)
private def ynT : MatQ := ([[⟨3, 1⟩]], 1)
private def xdT : MatQ := ([[⟨4, 1⟩]], 1)
private def ymidT : MatQ := ([[⟨16, 1⟩]], 4)
private def aT : Mat := [[⟨5, 1⟩]]
private def dmT : Mat := [[⟨1, 2⟩]]
private def dAsym : Mat := [[u, ⟨1001, 1⟩], [⟨1, 1001⟩, u]]

/-! The deviation's form expansion: the cleared difference `5 - 3`
reads its two members' own forms, the second at its swap, the
theorem route beside the decided display. -/

example : (quadForm (devQ xmT ymT).1 [⟨2, 1⟩]).oneValue
    ((quadForm xmT.1 [⟨2, 1⟩]).scale ymT.2
      + ((quadForm ymT.1 [⟨2, 1⟩]).swap).scale xmT.2) :=
  dev_expand xmT ymT [⟨2, 1⟩] rfl (by decide +kernel) rfl
    (by decide +kernel)
example : (quadForm (devQ xmT ymT).1 [⟨2, 1⟩]).oneValue
    ((quadForm xmT.1 [⟨2, 1⟩]).scale ymT.2
      + ((quadForm ymT.1 [⟨2, 1⟩]).swap).scale xmT.2) := by
  decide +kernel

/-! The deviation's triangle at the two caps: the members `5, 3, 2`
about the unit gram, the deviation `2` capped at `[2 : 1]` and the
deviation `1` at `[1 : 1]`, the middle member withdrawing and the
two caps' cross-collected weight pricing `5 - 2` at three against
three exactly. -/

example : capQ (devQ xmT ymT) gW 2 1 spK (spOne ⟨5, 1⟩) := by
  decide +kernel
example : capQ (devQ ymT ynT) gW 1 1 spK (spOne ⟨3, 1⟩) := by
  decide +kernel

example : (∀ w : List BPair, w.length = 1 →
      (quadForm (devQ xmT ynT).1 w).scale (1 * 1)
        ≤ (quadForm gW w).scale ((2 * 1 + 1 * 1) * (devQ xmT ynT).2))
    ∧ (∀ w : List BPair, w.length = 1 →
      ((quadForm gW w).scale
          ((2 * 1 + 1 * 1) * (devQ xmT ynT).2)).swap
        ≤ (quadForm (devQ xmT ynT).1 w).scale (1 * 1)) :=
  dev_triangle (o := 1) xmT ymT ynT gW 2 1 1 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun w hw => cap_hi (devQ xmT ymT) gW 2 1 spK (spOne ⟨5, 1⟩)
      (by decide +kernel) w hw)
    (fun w hw => cap_lo (devQ xmT ymT) gW 2 1 spK (spOne ⟨5, 1⟩)
      (by decide +kernel) w hw)
    (fun w hw => cap_hi (devQ ymT ynT) gW 1 1 spK (spOne ⟨3, 1⟩)
      (by decide +kernel) w hw)
    (fun w hw => cap_lo (devQ ymT ynT) gW 1 1 spK (spOne ⟨3, 1⟩)
      (by decide +kernel) w hw)

example : (quadForm (devQ xmT ynT).1 [⟨2, 1⟩]).scale (1 * 1)
    ≤ (quadForm gW [⟨2, 1⟩]).scale
      ((2 * 1 + 1 * 1) * (devQ xmT ynT).2) := by decide +kernel
example : ((quadForm gW [⟨2, 1⟩]).scale
      ((2 * 1 + 1 * 1) * (devQ xmT ynT).2)).swap
    ≤ (quadForm (devQ xmT ynT).1 [⟨2, 1⟩]).scale (1 * 1) := by
  decide +kernel

/-! The triangle's two cap binders, each refusal beside the parted
conclusion at its own collected weight: the leading cap starved at
`[1 : 1]` parts its own read and the upper side at three against
two, and the trailing cap's modulus doubled parts its read and the
upper side at six against five. -/

example : ¬ capQ (devQ xmT ymT) gW 1 1 spK (spOne ⟨5, 1⟩) := by
  decide +kernel
example : ¬ ((quadForm (devQ xmT ynT).1 [⟨2, 1⟩]).scale (1 * 1)
    ≤ (quadForm gW [⟨2, 1⟩]).scale
      ((1 * 1 + 1 * 1) * (devQ xmT ynT).2)) := by decide +kernel
example : ¬ capQ (devQ ymT ynT) gW 1 2 spK (spOne ⟨3, 1⟩) := by
  decide +kernel
example : ¬ ((quadForm (devQ xmT ynT).1 [⟨2, 1⟩]).scale (1 * 2)
    ≤ (quadForm gW [⟨2, 1⟩]).scale
      ((2 * 2 + 1 * 1) * (devQ xmT ynT).2)) := by decide +kernel

/-! Clause (ii)'s polarization at the promoted cross read: the
cross datum `-1` capped two-sidedly at the unit gram, the doubled
cross read at the weights `1, 1` priced against the two diagonal
gram reads at the vectors `1` and `2` — minus four and four
against five. -/

example : capQ ((dmT, 1) : MatQ) gW 1 1 (spOne ⟨3, 1⟩) spK := by
  decide +kernel

example : (((dotN [⟨2, 1⟩] (matVec dmT [⟨3, 1⟩])).scale (1 * 1)
        + (dotN [⟨2, 1⟩] (matVec dmT [⟨3, 1⟩])).scale (1 * 1)).scale 1
      ≤ ((dotN [⟨2, 1⟩] (matVec gW [⟨2, 1⟩])).scale (1 * 1)
          + (dotN [⟨3, 1⟩] (matVec gW [⟨3, 1⟩])).scale (1 * 1)).scale
        (1 * 1))
    ∧ ((((dotN [⟨2, 1⟩] (matVec dmT [⟨3, 1⟩])).scale (1 * 1)
        + (dotN [⟨2, 1⟩] (matVec dmT [⟨3, 1⟩])).scale
          (1 * 1)).swap).scale 1
      ≤ ((dotN [⟨2, 1⟩] (matVec gW [⟨2, 1⟩])).scale (1 * 1)
          + (dotN [⟨3, 1⟩] (matVec gW [⟨3, 1⟩])).scale (1 * 1)).scale
        (1 * 1)) :=
  cap_cross (n := 1) dmT gW (1 * 1) 1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (fun w hw => cap_hi ((dmT, 1) : MatQ) gW 1 1 (spOne ⟨3, 1⟩) spK
      (by decide +kernel) w hw)
    (fun w hw => cap_lo ((dmT, 1) : MatQ) gW 1 1 (spOne ⟨3, 1⟩) spK
      (by decide +kernel) w hw)
    [⟨2, 1⟩] [⟨3, 1⟩] rfl rfl 1 1

example : ((dotN [⟨2, 1⟩] (matVec dmT [⟨3, 1⟩])).scale (1 * 1)
      + (dotN [⟨2, 1⟩] (matVec dmT [⟨3, 1⟩])).scale (1 * 1)).scale 1
    ≤ ((dotN [⟨2, 1⟩] (matVec gW [⟨2, 1⟩])).scale (1 * 1)
        + (dotN [⟨3, 1⟩] (matVec gW [⟨3, 1⟩])).scale (1 * 1)).scale
      (1 * 1) := by decide +kernel
example : (((dotN [⟨2, 1⟩] (matVec dmT [⟨3, 1⟩])).scale (1 * 1)
      + (dotN [⟨2, 1⟩] (matVec dmT [⟨3, 1⟩])).scale
        (1 * 1)).swap).scale 1
    ≤ ((dotN [⟨2, 1⟩] (matVec gW [⟨2, 1⟩])).scale (1 * 1)
        + (dotN [⟨3, 1⟩] (matVec gW [⟨3, 1⟩])).scale (1 * 1)).scale
      (1 * 1) := by decide +kernel

/-! The polarization's symmetry binder, the one load-bearing
record: the antisymmetric two-by-two datum `1000 (E₁₂ - E₂₁)`
refuses the transpose read and the conclusion parts at the unit
vectors, two thousand against two — the two cap binders standing
at that datum, its quadratic form unit-valued at every vector. -/

example : ¬ matOneValue (transposeM dAsym) dAsym := by decide +kernel
example : ¬ ((((dotN [⟨2, 1⟩, u] (matVec dAsym [u, ⟨2, 1⟩])).scale
        (1 * 1)
      + (dotN [⟨2, 1⟩, u] (matVec dAsym [u, ⟨2, 1⟩])).scale
        (1 * 1)).scale 1)
    ≤ (((dotN [⟨2, 1⟩, u] (matVec (idMat 2) [⟨2, 1⟩, u])).scale (1 * 1)
        + (dotN [u, ⟨2, 1⟩] (matVec (idMat 2) [u, ⟨2, 1⟩])).scale
          (1 * 1)).scale 1)) := by decide +kernel

/-! Clause (iii)'s pricing at the tight center: the member `Y = 1`
about `Ŷ = 4` at the floor `y0 = 1` and radius `ρ = 3`, the
center's witness `1/4` contracting at `λ = 1/4` and the member's
own witness `1` priced at `λ∘ = 4/4` — the transfer factor's
image priced at sixteen against sixteen exactly. -/

example : capQ (devQ yT ycT) gW 3 1 (spOne ⟨7, 1⟩) spK := by
  decide +kernel
example : floorRead ycT gW 1 1 3 1 spK := by decide +kernel
example : contractRead (transfer ccT) gW gW 1 4 spK := by
  decide +kernel

example : ∀ w : List BPair, w.length = 1 →
    (quadForm gW (matVec (transfer cxT).1 w)).scale
        ((4 * (1 * 1)) * (4 * (1 * 1)))
      ≤ (quadForm gW w).scale
        ((1 * (1 * 1 + 3 * 1)) * (1 * (1 * 1 + 3 * 1))
          * (cxT.2 * cxT.2)) :=
  transfer_price (o := 1) (o' := 1) yT ycT cxT ccT btT gW gW
    1 4 1 1 3 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (ball_floor_of yT ycT gW 1 1 3 1 spK (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun w hw => cap_lo (devQ yT ycT) gW 3 1 (spOne ⟨7, 1⟩) spK
        (by decide +kernel) w hw))
    (fun w hw => cap_hi (devQ yT ycT) gW 3 1 (spOne ⟨7, 1⟩) spK
      (by decide +kernel) w hw)
    (fun w hw => cap_lo (devQ yT ycT) gW 3 1 (spOne ⟨7, 1⟩) spK
      (by decide +kernel) w hw)
    (fun w hw => contract_all (transfer ccT) gW gW 1 4 spK
      (by decide +kernel) w hw)

example : (quadForm gW (matVec (transfer cxT).1 [⟨2, 1⟩])).scale
      ((4 * (1 * 1)) * (4 * (1 * 1)))
    ≤ (quadForm gW [⟨2, 1⟩]).scale
      ((1 * (1 * 1 + 3 * 1)) * (1 * (1 * 1 + 3 * 1))
        * (cxT.2 * cxT.2)) := by decide +kernel

/-! The pricing's five isolating refusals, each anchor beside the
parted conclusion at its own forged constants: the floor forged at
`y0 = 2` parts its read and the price at sixty-four against
twenty-five; the cap starved at `ρ = 1` parts at sixteen against
four; the contraction starved at `λ = 1/5` parts at twenty-five
against sixteen; the member's witness forged at `2` parts its join
and the price at sixty-four against sixteen; and the center's
witness read against a bond forged at ten parts with the member's
own witness at that bond standing, the price at sixteen hundred
against sixteen. -/

private def cxF3 : MatQ := ([[⟨3, 1⟩]], 1)
private def btF : Mat := [[⟨11, 1⟩]]
private def cxF : MatQ := ([[⟨11, 1⟩]], 1)

example : ¬ floorRead ycT gW 2 1 3 1 spK := by decide +kernel
example : ¬ ((quadForm gW (matVec (transfer cxT).1 [⟨2, 1⟩])).scale
      ((4 * (2 * 1)) * (4 * (2 * 1)))
    ≤ (quadForm gW [⟨2, 1⟩]).scale
      ((1 * (2 * 1 + 3 * 1)) * (1 * (2 * 1 + 3 * 1))
        * (cxT.2 * cxT.2))) := by decide +kernel

example : ¬ capQ (devQ yT ycT) gW 1 1 (spOne ⟨5, 1⟩) spK := by
  decide +kernel
example : ¬ ((quadForm gW (matVec (transfer cxT).1 [⟨2, 1⟩])).scale
      ((4 * (1 * 1)) * (4 * (1 * 1)))
    ≤ (quadForm gW [⟨2, 1⟩]).scale
      ((1 * (1 * 1 + 1 * 1)) * (1 * (1 * 1 + 1 * 1))
        * (cxT.2 * cxT.2))) := by decide +kernel

example : ¬ contractRead (transfer ccT) gW gW 1 5 spK := by
  decide +kernel
example : ¬ ((quadForm gW (matVec (transfer cxT).1 [⟨2, 1⟩])).scale
      ((5 * (1 * 1)) * (5 * (1 * 1)))
    ≤ (quadForm gW [⟨2, 1⟩]).scale
      ((1 * (1 * 1 + 3 * 1)) * (1 * (1 * 1 + 3 * 1))
        * (cxT.2 * cxT.2))) := by decide +kernel

example : ¬ oneValueQ (mulQ yT cxF3) (ofM btT) := by decide +kernel
example : ¬ ((quadForm gW (matVec (transfer cxF3).1 [⟨2, 1⟩])).scale
      ((4 * (1 * 1)) * (4 * (1 * 1)))
    ≤ (quadForm gW [⟨2, 1⟩]).scale
      ((1 * (1 * 1 + 3 * 1)) * (1 * (1 * 1 + 3 * 1))
        * (cxF3.2 * cxF3.2))) := by decide +kernel

example : oneValueQ (mulQ yT cxF) (ofM btF) := by decide +kernel
example : ¬ oneValueQ (mulQ ycT ccT) (ofM btF) := by decide +kernel
example : ¬ ((quadForm gW (matVec (transfer cxF).1 [⟨2, 1⟩])).scale
      ((4 * (1 * 1)) * (4 * (1 * 1)))
    ≤ (quadForm gW [⟨2, 1⟩]).scale
      ((1 * (1 * 1 + 3 * 1)) * (1 * (1 * 1 + 3 * 1))
        * (cxF.2 * cxF.2))) := by decide +kernel

/-! Clause (iii)'s image deviation at the same family: the member
`1` and the center `4` join the boundary block `A = 4` through the
bond `1` at the images `3` and `15/4`, the deviation `-3/4` capped
two-sidedly at the modulus `λ∘ = 1` — minus three against twelve
and minus twelve against minus three. -/

example : (∀ w : List BPair, w.length = 1 →
      (quadForm (devQ xdT ymidT).1 w).scale (1 * 1 * 1)
        ≤ (quadForm gW w).scale (1 * 1 * 3 * (devQ xdT ymidT).2))
    ∧ (∀ w : List BPair, w.length = 1 →
      ((quadForm gW w).scale
          (1 * 1 * 3 * (devQ xdT ymidT).2)).swap
        ≤ (quadForm (devQ xdT ymidT).1 w).scale (1 * 1 * 1)) :=
  image_contract (o := 1) (o' := 1) yT xdT ycT ymidT cxT ccT
    aT btT gW gW 1 4 1 1 3 1 1 1 spK spK
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun w hw => cap_hi (devQ yT ycT) gW 3 1 (spOne ⟨7, 1⟩) spK
      (by decide +kernel) w hw)
    (fun w hw => cap_lo (devQ yT ycT) gW 3 1 (spOne ⟨7, 1⟩) spK
      (by decide +kernel) w hw)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : (quadForm (devQ xdT ymidT).1 [⟨2, 1⟩]).scale (1 * 1 * 1)
    ≤ (quadForm gW [⟨2, 1⟩]).scale
      (1 * 1 * 3 * (devQ xdT ymidT).2) := by decide +kernel
example : ((quadForm gW [⟨2, 1⟩]).scale
      (1 * 1 * 3 * (devQ xdT ymidT).2)).swap
    ≤ (quadForm (devQ xdT ymidT).1 [⟨2, 1⟩]).scale (1 * 1 * 1) := by
  decide +kernel

example : (∀ w : List BPair, w.length = 1 →
      (quadForm (devQ xdT ymidT).1 w).scale (1 * 1 * 1)
        ≤ (quadForm gW w).scale (1 * 1 * 3 * (devQ xdT ymidT).2))
    ∧ (∀ w : List BPair, w.length = 1 →
      ((quadForm gW w).scale
          (1 * 1 * 3 * (devQ xdT ymidT).2)).swap
        ≤ (quadForm (devQ xdT ymidT).1 w).scale (1 * 1 * 1)) :=
  image_contract_of (o := 1) (o' := 1) yT xdT ycT ymidT cxT ccT
    aT btT gW gW 1 4 1 1 3 1 1 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun w hw => cap_hi (devQ yT ycT) gW 3 1 (spOne ⟨7, 1⟩) spK
      (by decide +kernel) w hw)
    (fun w hw => cap_lo (devQ yT ycT) gW 3 1 (spOne ⟨7, 1⟩) spK
      (by decide +kernel) w hw)
    (floor_all ycT gW 1 1 3 1 spK (by decide +kernel)
      (by decide +kernel) (by decide +kernel))
    (contract_all (transfer ccT) gW gW 1 4 spK (by decide +kernel))
    (by decide +kernel)
    (fun h => Nat.noConfusion h)
    (by decide +kernel)

/-! The image deviation's tie binder: at the modulus `λ∘ = 1/4` the
tie identity refuses, four against sixteen, and the swap side parts
beside it at minus twelve against minus forty-eight. -/

example : ¬ (1 * (1 * (4 * 1)) = 1 * ((1 * 1 + 3 * 1) * 4)) := by
  decide +kernel
example : ¬ (((quadForm gW [⟨2, 1⟩]).scale
      (1 * 1 * 3 * (devQ xdT ymidT).2)).swap
    ≤ (quadForm (devQ xdT ymidT).1 [⟨2, 1⟩]).scale (4 * 4 * 1)) := by
  decide +kernel

/-! The polarization's two cap binders at the antisymmetric datum:
its form reads its own swap — the transpose's exchange composed
with the memberwise swap the datum reads back — so the form is
unit-valued at every vector and both caps hold against the
identity gram at the unit modulus, the symmetry binder alone
carrying the parted conclusion above. -/

private theorem dAsymSwap (w : List BPair) (hw : w.length = 2) :
    (quadForm dAsym w).oneValue (quadForm dAsym w).swap :=
  BPair.oneValue_trans
    (BPair.oneValue_symm
      (elim.dotN_transpose_flip dAsym 2 (by decide +kernel) w w hw hw))
    (BPair.oneValue_trans
      (elim.dotN_matVec_congrM (transposeM dAsym) (matSwap dAsym) w w
        (by decide +kernel))
      (inertia.quadForm_swap dAsym w))

private theorem idPsd2 (w : List BPair) (hw : w.length = 2) :
    BPair.unit ≤ quadForm (idMat 2) w :=
  ground.leB_of_not_lt
    (inertia.psd_all (idMat 2) (mkSplit 2 (idMat 2))
      (by decide +kernel) (by decide +kernel) w hw)

private theorem dAsymUnitLe (w : List BPair) (hw : w.length = 2) :
    BPair.unit ≤ quadForm dAsym w :=
  ground.unitLeOfSwap (Or.inl (BPair.oneValue_symm (dAsymSwap w hw)))

private theorem dAsymLeUnit (w : List BPair) (hw : w.length = 2) :
    quadForm dAsym w ≤ BPair.unit :=
  ground.leB_swap
    (ground.unitLeOfSwap (z := (quadForm dAsym w).swap)
      (Or.inl (dAsymSwap w hw)))

private theorem dAsymHi : ∀ w : List BPair, w.length = 2 →
    (quadForm dAsym w).scale 1
      ≤ (quadForm (idMat 2) w).scale (1 * 1) :=
  fun w hw =>
    ground.leB_scale
      (ground.leB_trans (dAsymLeUnit w hw) (idPsd2 w hw)) 1

private theorem dAsymLo : ∀ w : List BPair, w.length = 2 →
    ((quadForm (idMat 2) w).scale (1 * 1)).swap
      ≤ (quadForm dAsym w).scale 1 :=
  fun w hw =>
    ground.leB_scale
      (ground.leB_trans (ground.leB_swap (idPsd2 w hw))
        (dAsymUnitLe w hw)) 1

example : (quadForm dAsym [⟨2, 1⟩, u]).scale 1
    ≤ (quadForm (idMat 2) [⟨2, 1⟩, u]).scale (1 * 1) :=
  dAsymHi [⟨2, 1⟩, u] rfl
example : ∀ w : List BPair, w.length = 2 →
    (quadForm dAsym w).scale 1
      ≤ (quadForm (idMat 2) w).scale (1 * 1) := dAsymHi
example : ∀ w : List BPair, w.length = 2 →
    ((quadForm (idMat 2) w).scale (1 * 1)).swap
      ≤ (quadForm dAsym w).scale 1 := dAsymLo

/-! The member-symmetry records at order two: the unbalanced center
`Ŷ = diag(100, 2)` at the floor `y0 = 1` and radius `ρ = [1 : 1000]`,
the member `Y = Ŷ + K` at the antisymmetric bond deviation
`K = E₁₂ - E₂₁` — `K`'s form reads its own swap, so it is
unit-valued at every vector and the member sits inside every
radius, while the member's transfer factor and image deviation
read `100/201` against the modulus: the refused transpose read
parts `transfer_price`'s and `image_contract`'s conclusions with
every co-binder standing. -/

private def gI2 : Mat := idMat 2
private def g4S : Mat := [[⟨5, 1⟩]]
private def ycW : MatQ := ([[⟨101, 1⟩, u], [u, ⟨3, 1⟩]], 1)
private def xW : MatQ := ([[⟨101, 1⟩, ⟨2, 1⟩], [⟨1, 2⟩, ⟨3, 1⟩]], 1)
private def ccW : MatQ := ([[⟨2, 1⟩], [u]], 1)
private def cxW : MatQ := ([[⟨201, 1⟩], [⟨101, 1⟩]], 201)
private def bW : Mat := [[⟨101, 1⟩, u]]
private def ymidW : MatQ := ([[⟨101, 1⟩]], 1)
private def xdpW : MatQ := ([[⟨20201, 1⟩]], 201)
private def dKW : Mat := [[u, ⟨2, 1⟩], [⟨1, 2⟩, u]]
private def spF2 : Split 2 :=
  mkSplit 2 (siteDatum (matScale (1 * 1000) ycW.1)
    (matScale (1 * (1 * 1000 + 1 * 1)) gI2))

/-- An entrywise-antisymmetric datum's form reads its own swap:
the transpose's exchange composes with the memberwise swap the
datum reads back. -/
private theorem asymFormSwap (D : Mat) (n : Nat)
    (hr : rowsLen n D) (hl : D.length = n)
    (hs : matOneValue (transposeM D) (matSwap D)) :
    ∀ w : List BPair, w.length = n →
      (quadForm D w).oneValue (quadForm D w).swap :=
  fun w hw =>
    BPair.oneValue_trans
      (BPair.oneValue_symm
        (elim.dotN_transpose_flip D n hr w w hw (hw.trans hl.symm)))
      (BPair.oneValue_trans
        (elim.dotN_matVec_congrM (transposeM D) (matSwap D) w w hs)
        (inertia.quadForm_swap D w))

/-- A unit-capped form sits below any scaled form at or beyond the
unit. -/
private theorem capOfUnitHi (d g : BPair) (a b : Pos)
    (hd : d ≤ BPair.unit) (hg : BPair.unit ≤ g) :
    d.scale a ≤ g.scale b :=
  ground.leB_trans (ground.leB_scale hd a)
    (ground.leB_congr_left (ground.unitScale a)
      (ground.unitLeScale b hg))

/-- The swapped scaled form at or beyond the unit sits below any
form at or beyond it. -/
private theorem capOfUnitLo (d g : BPair) (a b : Pos)
    (hd : BPair.unit ≤ d) (hg : BPair.unit ≤ g) :
    (g.scale b).swap ≤ d.scale a :=
  ground.leB_trans (ground.leB_swap (ground.unitLeScale b hg))
    (ground.leB_trans
      (ground.leB_congr_right (ground.unitScale a)
        (ground.leB_refl BPair.unit))
      (ground.leB_scale hd a))

private theorem dKWSwap (w : List BPair) (hw : w.length = 2) :
    (quadForm dKW w).oneValue (quadForm dKW w).swap :=
  asymFormSwap dKW 2 (by decide +kernel) rfl (by decide +kernel) w hw

private theorem idPsd2W (w : List BPair) (hw : w.length = 2) :
    BPair.unit ≤ quadForm gI2 w :=
  ground.leB_of_not_lt
    (inertia.psd_all gI2 (mkSplit 2 gI2)
      (by decide +kernel) (by decide +kernel) w hw)

private theorem dKWUnitLe (w : List BPair) (hw : w.length = 2) :
    BPair.unit ≤ quadForm dKW w :=
  ground.unitLeOfSwap (Or.inl (BPair.oneValue_symm (dKWSwap w hw)))

private theorem dKWLeUnit (w : List BPair) (hw : w.length = 2) :
    quadForm dKW w ≤ BPair.unit :=
  ground.leB_swap
    (ground.unitLeOfSwap (z := (quadForm dKW w).swap)
      (Or.inl (dKWSwap w hw)))

private theorem qDW (w : List BPair) :
    (quadForm (devQ xW ycW).1 w).oneValue (quadForm dKW w) :=
  elim.dotN_matVec_congrM _ _ w w (by decide +kernel)

private theorem devWHi : ∀ w : List BPair, w.length = 2 →
    (quadForm (devQ xW ycW).1 w).scale 1000
      ≤ (quadForm gI2 w).scale (1 * (devQ xW ycW).2) :=
  fun w hw =>
    capOfUnitHi _ _ _ _
      (ground.leB_congr_left (BPair.oneValue_symm (qDW w))
        (dKWLeUnit w hw))
      (idPsd2W w hw)

private theorem devWLo : ∀ w : List BPair, w.length = 2 →
    ((quadForm gI2 w).scale (1 * (devQ xW ycW).2)).swap
      ≤ (quadForm (devQ xW ycW).1 w).scale 1000 :=
  fun w hw =>
    capOfUnitLo _ _ _ _
      (ground.leB_congr_right (BPair.oneValue_symm (qDW w))
        (dKWUnitLe w hw))
      (idPsd2W w hw)

/-! The standing co-binders: the shapes, the center's and gram's
symmetries, the witnesses and joins, the floor, the contraction,
the defect, the tie and the modulus, each decided; the caps at the
antisymmetric deviation the ∀-form witnesses above. -/

example : matOneValue (transposeM ycW.1) ycW.1 := by decide +kernel
example : matOneValue (transposeM gI2) gI2 := by decide +kernel
example : oneValueQ (mulQ xW cxW) (ofM (transposeM bW)) := by
  decide +kernel
example : oneValueQ (addQ xdpW (mulQ (ofM bW) cxW))
    (ofM ([[⟨201, 1⟩]] : Mat)) := by decide +kernel
example : oneValueQ (mulQ ycW ccW) (ofM (transposeM bW)) := by
  decide +kernel
example : oneValueQ (addQ ymidW (mulQ (ofM bW) ccW))
    (ofM ([[⟨201, 1⟩]] : Mat)) := by decide +kernel
example : floorRead ycW gI2 1 1 1 1000 spF2 := by decide +kernel
example : contractRead (transfer ccW) gI2 g4S 1 2 spK := by
  decide +kernel
example : capQ (devQ ymidW ymidW) g4S 1 2000 (spOne ⟨5, 1⟩)
    (spOne ⟨5, 1⟩) := by decide +kernel
example : (1 : Pos) * (1001 * (2 * 1000))
    = 1 * ((1 * 1000 + 1 * 1) * 2000) := by decide +kernel
example : (1 : Pos) * ((2000 * 2000) * 1000)
      + (1001 * 1001) * (1 * 2000)
    ≤ 1 * (2000 * (2000 * 2000)) := by decide +kernel
example : ∀ w : List BPair, w.length = 2 →
    (quadForm (devQ xW ycW).1 w).scale 1000
      ≤ (quadForm gI2 w).scale (1 * (devQ xW ycW).2) := devWHi
example : ∀ w : List BPair, w.length = 2 →
    ((quadForm gI2 w).scale (1 * (devQ xW ycW).2)).swap
      ≤ (quadForm (devQ xW ycW).1 w).scale 1000 := devWLo

/-! The refused member symmetry, and the two parted conclusions:
`transfer_price`'s at the transfer image's fifty thousand and
`image_contract`'s at the image deviation `100/201` against the
modulus. -/

example : ¬ matOneValue (transposeM xW.1) xW.1 := by decide +kernel
example : ¬ ((quadForm gI2
      (matVec (transfer cxW).1 [⟨2, 1⟩])).scale
      ((2 * (1 * 1000)) * (2 * (1 * 1000)))
    ≤ (quadForm g4S [⟨2, 1⟩]).scale
      ((1 * (1 * 1000 + 1 * 1)) * (1 * (1 * 1000 + 1 * 1))
        * (cxW.2 * cxW.2))) := by decide +kernel
example : ¬ ((quadForm (devQ xdpW ymidW).1 [⟨2, 1⟩]).scale
      (2000 * 2000 * 1000)
    ≤ (quadForm g4S [⟨2, 1⟩]).scale
      (1001 * 1001 * 1 * (devQ xdpW ymidW).2)) := by decide +kernel

/-! The pivot's upper-side read at the transported ball
(`ball_psd_of`): the two cap sides in their pointwise form with the
center's floor read the pivot's split at the upper side.  The pass
is the equal-membered pair at order one — the pivot `Y = 3` at its
own center `Ŷ = 3`, the unit gram, the floor `y0 = 1` and the
radius one — the deviation vacant so both cap matrices read the
gram, the floor's site datum reading one, the pivot's split at the
block `3` and the count vacant, decided raw and landed through the
theorem at the caps' `cap_hi`/`cap_lo` form. -/

private def pdX : greenprod.MatQ := ([[⟨4, 1⟩]], 1)
private def pdG : Mat := [[⟨2, 1⟩]]

example : floorRead pdX pdG 1 1 1 1 (spOne ⟨2, 1⟩) := by decide +kernel
example : capQ (devQ pdX pdX) pdG 1 1 (spOne ⟨2, 1⟩)
    (spOne ⟨2, 1⟩) := by decide +kernel
example : splitRead pdX.1 (spOne ⟨4, 1⟩) := by decide +kernel
example : psdAt (spOne ⟨4, 1⟩) := by decide +kernel

example : psdAt (spOne ⟨4, 1⟩) :=
  ball_psd_of (o := 1) (o' := 1) pdX pdX pdG 1 1 1 1 (spOne ⟨2, 1⟩)
    (spOne ⟨4, 1⟩) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (fun w hw => cap_hi (devQ pdX pdX) pdG 1 1 (spOne ⟨2, 1⟩)
      (spOne ⟨2, 1⟩) (by decide +kernel) w hw)
    (fun w hw => cap_lo (devQ pdX pdX) pdG 1 1 (spOne ⟨2, 1⟩)
      (spOne ⟨2, 1⟩) (by decide +kernel) w hw)
    (by decide +kernel)

/-! The same pivot read at ∀-form entries throughout
(`ball_psd_ptw`), the theorem route at the same data: the floor
read joins the two cap sides in its pointwise transport
(`floor_all`), and the pivot's split reads the upper side. -/

example : psdAt (spOne ⟨4, 1⟩) :=
  ball_psd_ptw (o := 1) (o' := 1) pdX pdX pdG 1 1 1 1
    (spOne ⟨4, 1⟩) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (fun w hw => floor_all pdX pdG 1 1 1 1 (spOne ⟨2, 1⟩)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      w hw)
    (fun w hw => cap_hi (devQ pdX pdX) pdG 1 1 (spOne ⟨2, 1⟩)
      (spOne ⟨2, 1⟩) (by decide +kernel) w hw)
    (fun w hw => cap_lo (devQ pdX pdX) pdG 1 1 (spOne ⟨2, 1⟩)
      (spOne ⟨2, 1⟩) (by decide +kernel) w hw)
    (by decide +kernel)

/-! The upper cap's binder is load-bearing, the record at the
indefinite gram of order two: `G = diag(1, -1)`, the center
`Ŷ = [[4,1],[1,-2]]` at the clearing two, the member
`Y = [[2,1],[1,0]]` at the same clearing, the floor pair `[1 : 2]`
and the radius one.  The deviation reads `diag(-4, 4)` at the
clearing four, so the lower cap side holds as an exact equality at
every vector — the swapped scaled gram and the deviation read one
value — while the upper side refuses at the vector `(-1, 2)`,
twelve against minus twelve.  The center's floor stands at the
congruence `Tᵀ ŶT` of the all-twos site datum to the block `2`
above a kernel of order one, the member's split reads the
indefinite block `[[2,1],[1,0]]` at the identity congruence, and
the conclusion parts there: that block's determinant is minus one,
one reversal. -/

private def gN : Mat := [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨1, 2⟩]]
private def ycN : greenprod.MatQ :=
  ([[⟨5, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 3⟩]], 2)
private def xN : greenprod.MatQ :=
  ([[⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 1⟩]], 2)

private def spFN : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 2⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨3, 1⟩], 1, rfl⟩

private def spXN : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩,
   [.two ⟨3, 1⟩ ⟨2, 1⟩ ⟨1, 1⟩], 0, rfl⟩

example : matOneValue (devQ xN ycN).1
    [[⟨1, 5⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨5, 1⟩]] := by decide +kernel
example : (devQ xN ycN).2 = 4 := by decide +kernel

example : sqAt xN.1 2 ∧ sqAt ycN.1 2 ∧ sqAt gN 2 := by decide +kernel
example : floorRead ycN gN 1 2 1 1 spFN := by decide +kernel
example : splitRead xN.1 spXN := by decide +kernel

/-- The lower cap side at the indefinite gram: the swapped scaled
gram and the deviation read one value, so the side is an equality
at every vector. -/
example : ∀ u : List BPair, u.length = 2 →
    ((quadForm gN u).scale (1 * (devQ xN ycN).2)).swap
      ≤ (quadForm (devQ xN ycN).1 u).scale 1 := by
  intro u _
  refine ground.leB_congr_right ?_ (ground.leB_refl _)
  refine BPair.oneValue_trans
    (BPair.oneValue_symm
      (ground.swap_congr (quadForm_scale (1 * (devQ xN ycN).2) gN u))) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_symm
      (quadForm_swap (matScale (1 * (devQ xN ycN).2) gN) u)) ?_
  refine BPair.oneValue_trans
    (elim.dotN_matVec_congrM (matSwap (matScale (1 * (devQ xN ycN).2) gN))
      (matScale 1 (devQ xN ycN).1) u u (by decide +kernel)) ?_
  exact quadForm_scale 1 (devQ xN ycN).1 u

example : ¬ ((quadForm (devQ xN ycN).1 [⟨1, 2⟩, ⟨3, 1⟩]).scale 1
    ≤ (quadForm gN [⟨1, 2⟩, ⟨3, 1⟩]).scale
      (1 * (devQ xN ycN).2)) := by decide +kernel
example : ¬ psdAt spXN := by decide +kernel

/-! The lower cap side's isolation (`ball_psd_of`): the member `-1`
at the center `3` about the unit gram sits below the ball — the
deviation `-4` reads the gram's swap at the quadruple scale, so the
upper cap side holds at every vector while the lower side refuses
at the unit vector, the floor standing, and the member's split
parting at its one lower entry. -/

private def loG : Mat := [[⟨2, 1⟩]]
private def loYc : greenprod.MatQ := ([[⟨4, 1⟩]], 1)
private def loX : greenprod.MatQ := ([[⟨1, 2⟩]], 1)

example : floorRead loYc loG 1 1 1 1 (spOne ⟨2, 1⟩) := by decide +kernel
example : splitRead loX.1 (spOne ⟨1, 2⟩) := by decide +kernel

example : ∀ u : List BPair, u.length = 1 →
    (quadForm (devQ loX loYc).1 u).scale 1
      ≤ (quadForm loG u).scale (1 * (devQ loX loYc).2) := by
  intro u hu
  have hpos : BPair.unit ≤ quadForm loG u :=
    ground.leB_of_not_lt
      (psd_all loG (spOne ⟨2, 1⟩) (by decide +kernel)
        (by decide +kernel) u hu)
  have hc : ((quadForm (devQ loX loYc).1 u).scale 1).oneValue
      ((((quadForm loG u).swap).scale 4).scale 1) := by
    refine BPair.scale_congr 1 ?_
    refine BPair.oneValue_trans
      (elim.dotN_matVec_congrM (devQ loX loYc).1
        (matScale 4 (matSwap loG)) u u (by decide +kernel)) ?_
    refine BPair.oneValue_trans (quadForm_scale 4 (matSwap loG) u) ?_
    exact BPair.scale_congr 4 (quadForm_swap loG u)
  refine ground.leB_congr_left (BPair.oneValue_symm hc) ?_
  refine ground.leB_trans
    (ground.leB_scale (ground.leB_scale (ground.leB_swap hpos) 4) 1) ?_
  refine ground.leB_congr_left
    (by decide +kernel :
      BPair.unit.oneValue ((BPair.unit.swap.scale 4).scale 1)) ?_
  exact ground.unitLeScale (1 * (devQ loX loYc).2) hpos

example : ¬ (((quadForm loG [⟨2, 1⟩]).scale
      (1 * (devQ loX loYc).2)).swap
    ≤ (quadForm (devQ loX loYc).1 [⟨2, 1⟩]).scale 1) := by
  decide +kernel
example : ¬ psdAt (spOne ⟨1, 2⟩) := by decide +kernel

/-! The floor's isolation (`ball_psd_of`): the member at its own
center `-1` about the unit gram reads a vacant deviation, both cap
sides at every vector, while the center's floor parts at its lower
read `-3` and the member's split parts at its one lower entry, the
deep member's parted cell above. -/

private def fYc : greenprod.MatQ := ([[⟨1, 2⟩]], 1)

example : splitRead (siteDatum (matScale (1 * 1) fYc.1)
    (matScale (fYc.2 * (1 * 1 + 1 * 1)) loG)) (spOne ⟨3, 6⟩) := by
  decide +kernel
example : ¬ psdAt (spOne ⟨3, 6⟩) := by decide +kernel
example : ¬ floorRead fYc loG 1 1 1 1 (spOne ⟨3, 6⟩) := by
  decide +kernel
example : splitRead fYc.1 (spOne ⟨1, 2⟩) := by decide +kernel

example : ∀ u : List BPair, u.length = 1 →
    (quadForm (devQ fYc fYc).1 u).scale 1
      ≤ (quadForm loG u).scale (1 * (devQ fYc fYc).2) := by
  intro u hu
  have hpos : BPair.unit ≤ quadForm loG u :=
    ground.leB_of_not_lt
      (psd_all loG (spOne ⟨2, 1⟩) (by decide +kernel)
        (by decide +kernel) u hu)
  have hz : ((quadForm (devQ fYc fYc).1 u).scale 1).oneValue
      BPair.unit := by
    refine BPair.oneValue_trans
      (BPair.scale_congr 1
        (BPair.oneValue_trans
          (elim.dotN_matVec_congrM (devQ fYc fYc).1
            (matAdd loG (matSwap loG)) u u (by decide +kernel))
          (BPair.oneValue_trans
            (quadForm_add_sq (o := 1) (by decide +kernel)
              (by decide +kernel) hu)
            (BPair.oneValue_trans
              (BPair.add_congr (BPair.oneValue_refl _)
                (quadForm_swap loG u))
              (BPair.oneValue_trans
                (BPair.oneValue_of_eq
                  (BPair.add_comm (quadForm loG u)
                    ((quadForm loG u).swap)))
                (BPair.swap_add_null
                  (BPair.oneValue_refl (quadForm loG u)))))))) ?_
    exact by decide +kernel
  refine ground.leB_congr_left (BPair.oneValue_symm hz) ?_
  exact ground.unitLeScale (1 * (devQ fYc fYc).2) hpos

example : ∀ u : List BPair, u.length = 1 →
    ((quadForm loG u).scale (1 * (devQ fYc fYc).2)).swap
      ≤ (quadForm (devQ fYc fYc).1 u).scale 1 := by
  intro u hu
  have hpos : BPair.unit ≤ quadForm loG u :=
    ground.leB_of_not_lt
      (psd_all loG (spOne ⟨2, 1⟩) (by decide +kernel)
        (by decide +kernel) u hu)
  have hz : ((quadForm (devQ fYc fYc).1 u).scale 1).oneValue
      BPair.unit := by
    refine BPair.oneValue_trans
      (BPair.scale_congr 1
        (BPair.oneValue_trans
          (elim.dotN_matVec_congrM (devQ fYc fYc).1
            (matAdd loG (matSwap loG)) u u (by decide +kernel))
          (BPair.oneValue_trans
            (quadForm_add_sq (o := 1) (by decide +kernel)
              (by decide +kernel) hu)
            (BPair.oneValue_trans
              (BPair.add_congr (BPair.oneValue_refl _)
                (quadForm_swap loG u))
              (BPair.oneValue_trans
                (BPair.oneValue_of_eq
                  (BPair.add_comm (quadForm loG u)
                    ((quadForm loG u).swap)))
                (BPair.swap_add_null
                  (BPair.oneValue_refl (quadForm loG u)))))))) ?_
    exact by decide +kernel
  refine ground.leB_congr_right (BPair.oneValue_symm hz) ?_
  exact ground.leB_swap (ground.unitLeScale (1 * (devQ fYc fYc).2) hpos)

/-! The orders' guard isolated at the collapsed shallower order:
`o = 0` with `o' = 1`, every further binder of `image_contract_of`
standing — the shape, exchange and tie reads decided, the
pointwise reads through the bridges at the vacant split and the
deeper gram's own split read, the vacant transfer reading the
contraction's left side at the sum's unit so the pointwise reads
reach no deeper datum — and the conclusion parted at the one-key
vector, the transported cap at one hundred against one. -/

private def nzQ : MatQ := (([] : elim.Mat), (1 : Pos))
private def nzGd : elim.Mat := idMat 1
private def nzA : elim.Mat := [[BPair.unit]]
private def nzB : elim.Mat := [[]]
private def nzXdp : MatQ := (([[BPair.ofNat 100]] : elim.Mat), (1 : Pos))
private def nzYmid : MatQ := (([[BPair.unit]] : elim.Mat), (1 : Pos))
private def sp0 : Split 0 := ⟨⟨[], rfl⟩, ⟨[], rfl⟩, [], 0, rfl⟩

example : sqAt nzQ.1 0 ∧ sqAt nzXdp.1 1 ∧ sqAt nzYmid.1 1
    ∧ rectAt nzQ.1 0 1 ∧ sqAt nzA 1 ∧ rectAt nzB 1 0
    ∧ sqAt (([] : elim.Mat)) 0
    ∧ matOneValue (transposeM nzQ.1) nzQ.1
    ∧ matOneValue (transposeM ([] : elim.Mat)) ([] : elim.Mat) := by
  decide +kernel

example : oneValueQ (mulQ nzQ nzQ) (ofM (transposeM nzB))
    ∧ oneValueQ (addQ nzXdp (mulQ (ofM nzB) nzQ)) (ofM nzA)
    ∧ oneValueQ (addQ nzYmid (mulQ (ofM nzB) nzQ)) (ofM nzA) := by
  decide +kernel

example : ∀ u : List BPair, u.length = 0 →
    (quadForm (devQ nzQ nzQ).1 u).scale 1
      ≤ (quadForm ([] : elim.Mat) u).scale (1 * (devQ nzQ nzQ).2) :=
  cap_hi (devQ nzQ nzQ) ([] : elim.Mat) 1 1 sp0 sp0 (by decide +kernel)

example : ∀ u : List BPair, u.length = 0 →
    ((quadForm ([] : elim.Mat) u).scale (1 * (devQ nzQ nzQ).2)).swap
      ≤ (quadForm (devQ nzQ nzQ).1 u).scale 1 :=
  cap_lo (devQ nzQ nzQ) ([] : elim.Mat) 1 1 sp0 sp0 (by decide +kernel)

example : ∀ u : List BPair, u.length = 0 →
    (quadForm ([] : elim.Mat) u).scale (nzQ.2 * (1 * 1 + 1 * 1))
      ≤ (quadForm nzQ.1 u).scale (1 * 1) :=
  floor_all nzQ ([] : elim.Mat) 1 1 1 1 sp0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : ∀ u : List BPair, u.length = 1 →
    (quadForm ([] : elim.Mat) (matVec (transfer nzQ).1 u)).scale (1 * 1)
      ≤ (quadForm nzGd u).scale (1 * 1 * (nzQ.2 * nzQ.2)) := by
  intro u hu
  have hpos : BPair.unit ≤ quadForm nzGd u :=
    ground.leB_of_not_lt
      (psd_all nzGd (spOne ⟨2, 1⟩) (by decide +kernel)
        (by decide +kernel) u hu)
  have hz : ((quadForm ([] : elim.Mat) ([] : List BPair)).scale
      (1 * 1)).oneValue BPair.unit := by decide +kernel
  refine ground.leB_congr_left (BPair.oneValue_symm hz) ?_
  exact ground.unitLeScale (1 * 1 * (nzQ.2 * nzQ.2)) hpos

example : (1 : Pos) * (2 * (1 * 1)) = 1 * ((1 * 1 + 1 * 1) * 1) := by
  decide +kernel

example : ¬ ((quadForm (devQ nzXdp nzYmid).1 [BPair.ofNat 1]).scale
      (1 * 1 * 1)
    ≤ (quadForm nzGd [BPair.ofNat 1]).scale
        (2 * 2 * 1 * (devQ nzXdp nzYmid).2)) := by decide +kernel
