import MassGap.Loopcap
/-!
The check module for `lem:loopcap`: the batteries re-read the loop
window's two-sided cap by kernel `decide` at the label calculus's
instantiation, the window the unit with one further letter,
`ls = (θ)`, so the label index is `(𝟏, θ)` at two letters.  The
shifted term is decided at three committed vectors — the occupied
pair `(1, 2)` at thirteen, the swap-signed `(1, -1)` at one, and
the unit vector at the sum's unit exactly — beside `shiftLower`'s
and `shiftUpper`'s own instances at the same window.  The
hypothesis terms are the interface's own decided reads, each window
Prop the Boolean fold over its key range: the composition read at
the fundamental `f = (1, 0)` with the intermediate list
`(f, (3, 0))`, the index's equality read, and the symmetry, row and
dimension reads `lem:fpcap`'s cap consumes.

The unit vector is the window's only sum-unit read: the shifted
term collects as `(u₀ + u₁)² + u₁²` at the walk's matrix
`[[0, 1], [1, 1]]`, so the swap-signed vector at one is the least
occupied value the window carries, and the boundary pin is the
unit vector's own.

The loop-cut tier is batteried twice.  At committed abstract lists
`cutSq`, `cutCap` and `cutForm` each run through the theorem with
each load-bearing hypothesis's isolating refusal beside them —
`hy` and `hx` at the display and at the image's read back, `hP` at
the image's read back, `hGc`, `hcap` and `hQ` at the form read —
and the length hypothesis carries the survival record
alone, the identity route's frame recorded at `coeff.dotP_sq_le`.
At the fundamental cut (`r = 1`, `d_f = 2`, the loop cut at
`A = U₁U₂U₃` against `U₄`) the coordinates enter cleared: the four
slots' joined lists read `144` at the pairing and `2 · 144` at both
self-pairings, so `cutCap`'s conclusion is the squared count `4`
against the gram; the window pair at the same clearing reads the
gram `144`, the image's gram `144` and the form at the sum's unit,
and `cutForm` returns the two-sided read.  The orthogonality pin
at `x = y = 𝟏` runs `cutSq` at the vacant contraction, the block
orthogonality's identity instance.
-/
set_option maxHeartbeats 16000000

open ground fusion elim loopcap

private def F : Data (List Nat) := dataA 2

private def ls : List (List Nat) := [adjchar.theta 2]

private def u1 : List BPair := [BPair.ofNat 1, BPair.ofNat 2]

private def u2 : List BPair := [BPair.ofNat 1, (BPair.ofNat 1).swap]

private def u0 : List BPair := [BPair.unit, BPair.unit]

/-! The loop window's magnetic matrix is the fusion form's own at
`θ` over the unit-headed list, the walk's `[[0, 1], [1, 1]]`. -/

example : pairpencil.loopMag F ls
    = fpcap.fusionMat F F.theta (F.unit :: ls) := rfl

example : pairpencil.loopMag F ls
    = [[BPair.ofNat 0, BPair.ofNat 1],
       [BPair.ofNat 1, BPair.ofNat 1]] := by decide +kernel

/-! The shifted term at three committed vectors: the occupied pair,
the swap-signed pair at the window's least occupied value, and the
unit vector at the sum's unit exactly. -/

example : (dotN u1 u1
      + inertia.quadForm (pairpencil.loopMag F ls) u1).oneValue
    (BPair.ofNat 13) := by decide +kernel

example : (dotN u2 u2
      + inertia.quadForm (pairpencil.loopMag F ls) u2).oneValue
    (BPair.ofNat 1) := by decide +kernel

example : (dotN u0 u0
      + inertia.quadForm (pairpencil.loopMag F ls) u0).oneValue
    BPair.unit := by decide +kernel

/-! The upper side's decided values at the same vectors: the `θ`
dimension against the gram. -/

example : ¬ (BPair.ofNat (F.dim F.theta) * dotN u1 u1
    < inertia.quadForm (pairpencil.loopMag F ls) u1) := by
  decide +kernel

example : ¬ (BPair.ofNat (F.dim F.theta) * dotN u2 u2
    < inertia.quadForm (pairpencil.loopMag F ls) u2) := by
  decide +kernel

/-! The interface's hypothesis terms at the window, each the
decided fold at the window's key range. -/

private theorem symWin : fpcap.symAt F F.theta (F.unit :: ls) := by
  decide +kernel

private theorem rowWin : fpcap.rowCap F F.theta (F.unit :: ls) := by
  decide +kernel

private theorem dimWin : fpcap.dimPos F (F.unit :: ls) := by decide +kernel

private theorem compWin :
    fpcap.compRead F [1, 0] (F.unit :: ls) [[1, 0], [3, 0]] := by
  decide +kernel

private theorem distWin : fpcap.distinctAt F (F.unit :: ls) := by
  decide +kernel

/-! The theorems' own instances at the window, both sides at both
occupied vectors. -/

example : ¬ (dotN u1 u1
      + inertia.quadForm (pairpencil.loopMag F ls) u1
    < BPair.unit) :=
  shiftLower F [1, 0] ls [[1, 0], [3, 0]] compWin distWin u1 rfl

example : ¬ (dotN u2 u2
      + inertia.quadForm (pairpencil.loopMag F ls) u2
    < BPair.unit) :=
  shiftLower F [1, 0] ls [[1, 0], [3, 0]] compWin distWin u2 rfl

example : ¬ (dotN u0 u0
      + inertia.quadForm (pairpencil.loopMag F ls) u0
    < BPair.unit) :=
  shiftLower F [1, 0] ls [[1, 0], [3, 0]] compWin distWin u0 rfl

example : ¬ (BPair.ofNat (F.dim F.theta) * dotN u1 u1
    < inertia.quadForm (pairpencil.loopMag F ls) u1) :=
  shiftUpper F ls symWin rowWin dimWin u1 rfl

example : ¬ (BPair.ofNat (F.dim F.theta) * dotN u2 u2
    < inertia.quadForm (pairpencil.loopMag F ls) u2) :=
  shiftUpper F ls symWin rowWin dimWin u2 rfl

/-! The committed refusal at the repeated-label window: `hdist` is
the one hypothesis between the rest and a false read.  At the
index `(𝟏, θ, θ, [4,0], [4,0])` the composition read holds at the
fundamental's full intermediate list, yet the shifted term reads
strictly below the sum's unit at the exhibited vector — the
window's labels pairwise distinct is `lem:loopcap`'s own index
structure, the set the list carries. -/

private def lsBad : List (List Nat) :=
  [adjchar.theta 2, adjchar.theta 2, [4, 0], [4, 0]]

private def ub : List BPair :=
  [(BPair.ofNat 3).swap, BPair.ofNat 1, BPair.ofNat 2,
   (BPair.ofNat 1).swap, (BPair.ofNat 1).swap]

example : dotN ub ub
      + inertia.quadForm (pairpencil.loopMag F lsBad) ub
    < BPair.unit := by decide +kernel

example : fpcap.compRead F [1, 0] (F.unit :: lsBad)
    [[1, 0], [3, 0], [5, 0]] := by decide +kernel

/-! The three-letter window `(𝟏, θ, [4,0])`: the interior row
exercises the fold exchange off the head, the row folds tight at
two of the three keys. -/

private def ls3 : List (List Nat) := [adjchar.theta 2, [4, 0]]

private def u3 : List BPair :=
  [BPair.ofNat 1, (BPair.ofNat 2).swap, BPair.ofNat 1]

example : ¬ (BPair.ofNat (F.dim F.theta) * dotN u3 u3
    < inertia.quadForm (pairpencil.loopMag F ls3) u3) :=
  shiftUpper F ls3 (by decide +kernel) (by decide +kernel) (by decide +kernel) u3 rfl

/-! The loop-cut tier at committed abstract lists: the display, the
order's read back at the image, and the two-sided form read, each
through its theorem with the dropped hypothesis's own refusal
beside it. -/

private def ya1 : List BPair := [⟨2, 1⟩, ⟨2, 1⟩]

private def xb1 : List BPair := [⟨3, 1⟩, ⟨1, 3⟩]

private def xb2 : List BPair := [⟨3, 1⟩, ⟨1, 1⟩]

/-- The display at the vacant pairing: the two self-pairings read
`2 = 2 · 1` and `8 = 2 · 4`, the cross fold vacant, and the
squared comparison holds outright. -/
example : (dotP ya1 ya1).oneValue (BPair.ofNat 2 * ⟨2, 1⟩) := by decide +kernel

example : (dotP xb1 xb1).oneValue (BPair.ofNat 2 * ⟨5, 1⟩) := by decide +kernel

example : (dotP ya1 xb1).oneValue BPair.unit := by decide +kernel

example : ¬ (BPair.ofNat 2 * ⟨2, 1⟩ * (BPair.ofNat 2 * ⟨5, 1⟩)
    < dotP ya1 xb1 * dotP ya1 xb1) := by decide +kernel

example : ¬ (BPair.ofNat 2 * ⟨2, 1⟩ * (BPair.ofNat 2 * ⟨5, 1⟩)
    < dotP ya1 xb1 * dotP ya1 xb1) :=
  cutSq ya1 xb1 rfl 2 ⟨2, 1⟩ ⟨5, 1⟩ (by decide +kernel) (by decide +kernel)

/-- The display at an occupied pairing: the pairing's square reads
`4` against the grams' product `8`, the gap the cross fold's. -/
example : (dotP xb2 xb2).oneValue (BPair.ofNat 2 * ⟨3, 1⟩) := by decide +kernel

example : (dotP ya1 xb2).oneValue (BPair.ofNat 2) := by decide +kernel

example : ¬ (BPair.ofNat 2 * ⟨2, 1⟩ * (BPair.ofNat 2 * ⟨3, 1⟩)
    < dotP ya1 xb2 * dotP ya1 xb2) :=
  cutSq ya1 xb2 rfl 2 ⟨2, 1⟩ ⟨3, 1⟩ (by decide +kernel) (by decide +kernel)

/-- Refusal isolating `hy` at the display: at `ya = (2)`,
`xb = (1)` and the count's unit the second self-pairing still reads
`1 = 1 · 1`, while the first reads `4` against `1` and refuses, and
the conclusion parts — the count's square `1` sits strictly below
the pairing's square `4`. -/
example : ¬ (dotP [(⟨3, 1⟩ : BPair)] [(⟨3, 1⟩ : BPair)]).oneValue
    (BPair.ofNat 1 * ⟨2, 1⟩) := by decide +kernel

example : (dotP [(⟨2, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)]).oneValue
    (BPair.ofNat 1 * ⟨2, 1⟩) := by decide +kernel

example : BPair.ofNat 1 * ⟨2, 1⟩ * (BPair.ofNat 1 * ⟨2, 1⟩)
    < dotP [(⟨3, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)]
      * dotP [(⟨3, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)] := by decide +kernel

/-- The image's read back at the unit count: the pairing, the two
self-pairings and the conclusion all read `1`. -/
example : (dotP [(⟨2, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)]).oneValue
    (⟨2, 1⟩ : BPair) := by decide +kernel

example : ¬ (BPair.ofNat (1 * 1) * ⟨2, 1⟩ < (⟨2, 1⟩ : BPair)) := by
  decide +kernel

example : ¬ (BPair.ofNat (1 * 1) * ⟨2, 1⟩ < (⟨2, 1⟩ : BPair)) :=
  cutCap [⟨2, 1⟩] [⟨2, 1⟩] rfl 1 ⟨2, 1⟩ ⟨2, 1⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Refusal isolating `hy` at the image's read back: the pairing
pins `N = 2` and the second self-pairing still reads `1 = 1 · 1`,
while the first reads `4` against `1 · 2` and refuses; the squared
count against the gram then sits strictly below `N`. -/
example : (dotP [(⟨3, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)]).oneValue
    (⟨3, 1⟩ : BPair) := by decide +kernel

example : ¬ (dotP [(⟨3, 1⟩ : BPair)] [(⟨3, 1⟩ : BPair)]).oneValue
    (BPair.ofNat 1 * ⟨3, 1⟩) := by decide +kernel

example : BPair.ofNat (1 * 1) * ⟨2, 1⟩ < (⟨3, 1⟩ : BPair) := by decide +kernel

/-- The two-sided form read at the unit count: the window's gram
reads `1`, the form reads `1`, and both the form and its swap sit
at or below the count against the gram. -/
example : (dotP [(⟨2, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)]).oneValue
    (BPair.ofNat 1) := by decide +kernel

example : ¬ (BPair.ofNat (1 * 1) * BPair.ofNat 1
    < dotP [(⟨2, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)]) := by decide +kernel

example : (⟨2, 1⟩ : BPair) ≤ BPair.ofNat 1 * BPair.ofNat 1
    ∧ (⟨2, 1⟩ : BPair).swap ≤ BPair.ofNat 1 * BPair.ofNat 1 :=
  cutForm [⟨2, 1⟩] [⟨2, 1⟩] rfl 1 (BPair.ofNat 1) ⟨2, 1⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Refusal isolating `hGc` at the form read: the form reads `3`
and the cap holds at `1`, while the window's gram reads `9`
against the stated `1` and refuses; the form then sits strictly
above the count against the stated gram. -/
example : ¬ (dotP [(⟨4, 1⟩ : BPair)] [(⟨4, 1⟩ : BPair)]).oneValue
    (⟨2, 1⟩ : BPair) := by decide +kernel

example : (⟨4, 1⟩ : BPair).oneValue
    (dotP [(⟨4, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)]) := by decide +kernel

example : ¬ (BPair.ofNat (1 * 1) * ⟨2, 1⟩
    < dotP [(⟨2, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)]) := by decide +kernel

example : ¬ ((⟨4, 1⟩ : BPair) ≤ BPair.ofNat 1 * ⟨2, 1⟩) := by decide +kernel

/-- Refusal isolating `hcap` at the form read: the window's gram
reads `1` and the form reads `2`, while the image's own gram reads
`4` above the squared count's `1` and the cap refuses; the form
then sits strictly above the count against the gram. -/
example : (dotP [(⟨2, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)]).oneValue
    (⟨2, 1⟩ : BPair) := by decide +kernel

example : (⟨3, 1⟩ : BPair).oneValue
    (dotP [(⟨2, 1⟩ : BPair)] [(⟨3, 1⟩ : BPair)]) := by decide +kernel

example : BPair.ofNat (1 * 1) * ⟨2, 1⟩
    < dotP [(⟨3, 1⟩ : BPair)] [(⟨3, 1⟩ : BPair)] := by decide +kernel

example : ¬ ((⟨3, 1⟩ : BPair) ≤ BPair.ofNat 1 * ⟨2, 1⟩) := by decide +kernel

/-! The remaining load-bearing binders' isolating refusals: `hx`
at the display and at the image's read back, `hP` at the image's
read back, and `hQ` at the form read — each dropped hypothesis's
own refusal with every other hypothesis held at the committed
data. -/

/-- Refusal isolating `hx` at the display: the first self-pairing
reads `1 = 1 · 1` while the second reads `1` against the stated
`-1` and refuses, and the conclusion parts — the grams' product
sits strictly below the pairing's square. -/
example : (dotP [(⟨2, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)]).oneValue
    (BPair.ofNat 1 * ⟨2, 1⟩) := by decide +kernel

example : ¬ (dotP [(⟨2, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)]).oneValue
    (BPair.ofNat 1 * ⟨1, 2⟩) := by decide +kernel

example : BPair.ofNat 1 * ⟨2, 1⟩ * (BPair.ofNat 1 * ⟨1, 2⟩)
    < dotP [(⟨2, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)]
      * dotP [(⟨2, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)] := by decide +kernel

/-- Refusal isolating `hP` at the image's read back: at the vacant
lists and the vacant count both contractions hold at the stated
data, while the pairing reads the sum's unit against the stated
`1` and refuses; the vacant count against the gram sits strictly
below the stated `N`. -/
example : (dotP [BPair.unit] [BPair.unit]).oneValue
    (BPair.ofNat 0 * ⟨2, 1⟩) := by decide +kernel

example : (dotP [BPair.unit] [BPair.unit]).oneValue
    (BPair.ofNat 0 * BPair.unit) := by decide +kernel

example : ¬ (dotP [BPair.unit] [BPair.unit]).oneValue
    (⟨2, 1⟩ : BPair) := by decide +kernel

example : BPair.ofNat (0 * 0) * BPair.unit < (⟨2, 1⟩ : BPair) := by
  decide +kernel

/-- Refusal isolating `hx` at the image's read back: the pairing
pins `N = 1` and the first contraction holds at the unit-count
pins above, while the second self-pairing reads `1` against the
stated `-1` and refuses; the squared count against the stated
gram sits strictly below `N`. -/
example : ¬ (dotP [(⟨2, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)]).oneValue
    (BPair.ofNat 1 * (⟨1, 2⟩ : BPair)) := by decide +kernel

example : BPair.ofNat (1 * 1) * ⟨1, 2⟩ < (⟨2, 1⟩ : BPair) := by
  decide +kernel

/-- Refusal isolating `hQ` at the form read: the window's gram and
the cap hold at the unit-count pins above, while the form reads
`1` against the stated `3` and refuses; the stated form sits
strictly above the count against the gram. -/
example : ¬ ((⟨4, 1⟩ : BPair)).oneValue
    (dotP [(⟨2, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)]) := by decide +kernel

example : ¬ ((⟨4, 1⟩ : BPair) ≤ BPair.ofNat 1 * BPair.ofNat 1) := by
  decide +kernel

/-- The image's read back at the vacant count, through the theorem:
the contraction at the count's unit forces the vacant lists and
the conclusion reads outright, the vacant arm's own route. -/
example : ¬ (BPair.ofNat (0 * 0) * BPair.unit < BPair.unit) :=
  cutCap [BPair.unit] [BPair.unit] rfl 0 BPair.unit BPair.unit
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The length hypothesis is the identity route's frame, the
classification recorded at `coeff.dotP_sq_le`: the folds truncate
at the shorter list and the further self-pairing members enter as
squares, so at mismatched lists every remaining hypothesis and
every conclusion still reads true.  The survival record is
committed, one instance per theorem. -/

private def yaS : List BPair := [⟨2, 1⟩, ⟨1, 1⟩]

/-- The display's survival at the mismatched pair: `ya1` against
the one-place `(2)`, the truncated pairing reading `2` against the
grams' product `8`, the first self-pairing's pin standing above. -/
example : (dotP [(⟨3, 1⟩ : BPair)] [(⟨3, 1⟩ : BPair)]).oneValue
    (BPair.ofNat 2 * ⟨3, 1⟩) := by decide +kernel

example : ¬ (BPair.ofNat 2 * ⟨2, 1⟩ * (BPair.ofNat 2 * ⟨3, 1⟩)
    < dotP ya1 [⟨3, 1⟩] * dotP ya1 [⟨3, 1⟩]) := by decide +kernel

/-- The image's read back at the mismatched pair: the truncated
pairing pins `N = 1` and the two self-pairings read `1`. -/
example : (dotP yaS [⟨2, 1⟩]).oneValue (⟨2, 1⟩ : BPair) := by decide +kernel

example : (dotP yaS yaS).oneValue (BPair.ofNat 1 * ⟨2, 1⟩) := by decide +kernel

example : (dotP [(⟨2, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)]).oneValue
    (BPair.ofNat 1 * ⟨2, 1⟩) := by decide +kernel

example : ¬ (BPair.ofNat (1 * 1) * ⟨2, 1⟩ < (⟨2, 1⟩ : BPair)) := by
  decide +kernel

/-- The form read at the mismatched pair: the window's gram reads
`1`, the form reads `1`, and both sides of the conclusion hold. -/
example : (dotP yaS yaS).oneValue (BPair.ofNat 1) := by decide +kernel

example : (⟨2, 1⟩ : BPair).oneValue (dotP yaS [⟨2, 1⟩]) := by decide +kernel

example : ¬ (BPair.ofNat (1 * 1) * BPair.ofNat 1
    < dotP [(⟨2, 1⟩ : BPair)] [(⟨2, 1⟩ : BPair)]) := by decide +kernel

example : (⟨2, 1⟩ : BPair) ≤ BPair.ofNat 1 * BPair.ofNat 1
    ∧ (⟨2, 1⟩ : BPair).swap ≤ BPair.ofNat 1 * BPair.ofNat 1 := by
  decide +kernel

/-! Tier 2 — the fundamental cut at the coefficient carrier, `r = 1`
and `d_f = 2`, the loop cut at `A = U₁U₂U₃` against `U₄`, the
path's three links one edge at the convolution identity
(`thm:network`(i)).  The block
scales `[1:d_λ]` are the gram's weights, not carrier values, so
every committed list enters cleared at the homogeneity principle: a
coordinate of gram weight `w · [1:n]` enters as `w · n` copies of
the `[1:n]`-scaled value and every pairing is the plain fold, the
clearing factor `c` common to both slot sides and `e` to the window
pair.

The slots `(i, j)` run `(1,1), (1,2), (2,1), (2,2)`.  At the dual
exchange `Ā_{ij} = ε_{ii'} ε_{jj'} A_{i'j'}` with `i' = 3 - i`,
`j' = 3 - j` and `ε₁₂ = 1 = -ε₂₁`, the slot's sign is `σ(ij) = +1`
at `i = j` and `-1` otherwise.  The tensor square splits at
`A_{pq} A_{kl} = T_{(pk)(ql)} + [1:2] · ε_{pk} ε_{ql}`, so the slot's
element `σ(ij) · Σ_{kl} A_{i'j'} A_{kl} ⊗ (U₄)_{lk}` splits at
`(p, q) = (i', j')` into a unit-channel part and a `θ`-part.

The unit channel: `Σ_{kl} ε_{i'k} ε_{j'l} (U₄)_{lk} = ε_{i'i} ε_{j'j}
(U₄)_{ji}` and `ε_{i'i} ε_{j'j} = σ(ij)`, so the coefficient is
`σ(ij)² · [1:2] = +[1:2]` at every slot, on the coordinate
`𝟏_A ⊗ f_{U₄}` at `(j, i)` of gram weight `1 · [1:2]`.  That
coordinate is the one the two sides share; the `U₄` side's value
there is `1`.

The `θ` channel at the `m`-list `m₁ = v₁⊗v₁`, `m₂ = v₁⊗v₂ + v₂⊗v₁`,
`m₃ = v₂⊗v₂` (gram `diag(1, 2, 1)`): with `P` the symmetrizer,
`P(e_q ⊗ e_l) = Σ_b S^{(ql)}_b m_b` at `S^{(11)} = (1,0,0)`,
`S^{(12)} = S^{(21)} = (0, [1:2], 0)`, `S^{(22)} = (0,0,1)`, and
`T_{(pk)(ql)} = Σ_{ab} S^{(pk)}_a G_{aa} M_{ab} S^{(ql)}_b` at the
`θ`-matrix `M` in the `m`-list.  The slot's `θ` coefficient on
`(θ_A at (a,b)) ⊗ (f_{U₄} at (l,k))` is therefore
`σ(ij) · S^{(i'k)}_a G_{aa} S^{(j'l)}_b`; since `S^{(pk)}_a G_{aa} = 1`
at the single occupied `a` of each `(p,k)`, the value is `σ(ij)` at
`j' = l` and `σ(ij) · [1:2]` at `j' ≠ l`, one coordinate per
`(k, l)`, four per slot, the slots joined at `con:coeff`'s one
list.

The `θ_A` weights are `[1:3] · (G⁻¹)_{aa} · G_{bb}` at `d_θ = 3`,
the `f_{U₄}` weight `[1:2]`, so the four coordinates carry weights
`[1:6]` at `(i' = k, j' = l)`, `[1:3]` at `(i' = k, j' ≠ l)`,
`[1:12]` at `(i' ≠ k, j' = l)` and `[1:6]` at `(i' ≠ k, j' ≠ l)`,
hence copy counts `6, 3, 12, 6` and cleared entries `2σ, 2σ, σ, σ`
at `c = 12` — the least clearing, the `[1:12]` weight forcing
`12 ∣ c`.  Their contributions `[1:6] + [1:12] + [1:12] + [1:24]`
sum to `[3:8]`, so the slot's `ya` self-pairing is
`[1:8] + [3:8] = [1:2]` uncleared, `18 + 54 = 72` at `c = 12`; the
slot's `xb` self-pairing is `[1:2]` uncleared, `72` cleared, and
the shared coordinate gives the cross read `[1:4]` uncleared, `36`
cleared. -/

/-- The `+1`-signed slot's `ya` coordinates: the shared unit-channel
coordinate's two copies, then the four `θ` coordinates at their
copy counts. -/
private def yaPos : List BPair :=
  [BPair.ofNat 3, BPair.ofNat 3]
    ++ List.replicate 6 (BPair.ofNat 2)
    ++ List.replicate 3 (BPair.ofNat 2)
    ++ List.replicate 12 (BPair.ofNat 1)
    ++ List.replicate 6 (BPair.ofNat 1)

/-- The `-1`-signed slot's `ya` coordinates: the unit channel reads
`+[1:2]` at every slot, so only the `θ` coordinates carry the
sign. -/
private def yaNeg : List BPair :=
  [BPair.ofNat 3, BPair.ofNat 3]
    ++ List.replicate 6 (BPair.ofNat 2).swap
    ++ List.replicate 3 (BPair.ofNat 2).swap
    ++ List.replicate 12 (BPair.ofNat 1).swap
    ++ List.replicate 6 (BPair.ofNat 1).swap

/-- The slot's `xb` coordinates: the shared coordinate's two copies
at the `U₄` value `1`, the `θ` frame vacant. -/
private def xbSlot : List BPair :=
  [BPair.ofNat 6, BPair.ofNat 6] ++ List.replicate 27 BPair.unit

/-- The four slots joined at the signs `+, -, -, +`. -/
private def cutYA : List BPair := yaPos ++ yaNeg ++ yaNeg ++ yaPos

private def cutXB : List BPair := xbSlot ++ xbSlot ++ xbSlot ++ xbSlot

/-! The slot reads: `72`, `72` and `36`, the joined reads their
fourfold. -/

example : (dotP yaPos yaPos).oneValue (BPair.ofNat 72) := by decide +kernel

example : (dotP yaNeg yaNeg).oneValue (BPair.ofNat 72) := by decide +kernel

example : (dotP xbSlot xbSlot).oneValue (BPair.ofNat 72) := by decide +kernel

example : (dotP yaPos xbSlot).oneValue (BPair.ofNat 36) := by decide +kernel

example : (dotP yaNeg xbSlot).oneValue (BPair.ofNat 36) := by decide +kernel

/-- The joined pairing is the cut datum `N = 144`. -/
example : (dotP cutYA cutXB).oneValue (BPair.ofNat 144) := by decide +kernel

/-- The joined self-pairings read the count `d_f = 2` against the
grams, both sides at `144`. -/
example : (dotP cutYA cutYA).oneValue
    (BPair.ofNat 2 * BPair.ofNat 144) := by decide +kernel

example : (dotP cutXB cutXB).oneValue
    (BPair.ofNat 2 * BPair.ofNat 144) := by decide +kernel

/-- The image's read back at the cut datum, through the theorem. -/
private theorem cutBound : ¬ (BPair.ofNat (2 * 2) * BPair.ofNat 144
    < BPair.ofNat 144) :=
  cutCap cutYA cutXB rfl 2 (BPair.ofNat 144) (BPair.ofNat 144)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The window pair at the clearing `e = 12`: the vector `x = 𝟏` on
the unit block at weight `1`, its image `χ_f x` on the `f ⊗ f`
block's four coordinates at weight `[1:4]`, four copies each. -/

/-- The window vector: the unit block's single cleared entry, the
image's frame vacant. -/
private def winXC : List BPair :=
  BPair.ofNat 12 :: List.replicate 16 BPair.unit

/-- The image `χ_f x`: the unit block vacant, the four image
coordinates at value `1`, cleared `12 · [1:4] = 3`. -/
private def winMXC : List BPair :=
  BPair.unit :: List.replicate 16 (BPair.ofNat 3)

/-- The window's gram, cleared: `⟨x, x⟩ = 1` at `e² = 144`, the
`Gx` the form read consumes. -/
example : (dotP winXC winXC).oneValue (BPair.ofNat 144) := by decide +kernel

/-- The coherence pin tying the window to the cut datum:
`⟨χ_f x, χ_f x⟩ = 1` reads the same `144`. -/
private theorem winCoh :
    (dotP winMXC winMXC).oneValue (BPair.ofNat 144) := by decide +kernel

/-- The form at the window: `⟨x, χ_f x⟩` vacant. -/
example : BPair.unit.oneValue (dotP winXC winMXC) := by decide +kernel

/-- The two-sided form read through the theorem, the cap the cut
datum's own conclusion carried across the coherence pin — the
composition's tie the one clearing, `c = e = 12` on both
realizations. -/
example : BPair.unit ≤ BPair.ofNat 2 * BPair.ofNat 144
    ∧ BPair.unit.swap ≤ BPair.ofNat 2 * BPair.ofNat 144 :=
  cutForm winXC winMXC rfl 2 (BPair.ofNat 144) BPair.unit
    (by decide +kernel) (by decide +kernel)
    (fun hlt => cutBound
      (BPair.lt_congr (BPair.oneValue_refl _) winCoh hlt))

/-! The member cut at the `θ`-block (`lem:loopcap`'s member clause,
`r = 1`, `d_θ = 3`): the cut split is the trace read over the
stated `m`-list (`lem:lowerspan`'s trace read at the Gram
`diag(1, 2, 1)`), the middle solve at the diagonal Gram, the slot
weights `[w_a : 2 G_bb]` at the trace tie `w_a G_aa = 2`; the
weights absorb symmetrically into the slot pair at
`[1 : G_aa G_bb]` apiece, so each slot's two self-pairings read
the flat `[1:3]` at the block orthogonality's `[1:3] G_aa G_bb`
(`con:coeff`), and the contraction reads `9 · [1:3] = 3 = d_θ`,
the evaluation identity at the block.  The trace element's
coordinates are the deltas at the mixed frame, its self-pairing
`3 · [1:3] = 1`.  Cleared at `c = e = 3`: each slot's list is
three entries of one on its own side of the slot frame, the
joined reads `27 = 3 · 9` at both contractions with the cross
read vacant (`⟨𝟏, χ_θ 𝟏⟩` the unit coefficient's), and the
window pair reads the gram `9`, the image's gram `9` and the
form at the sum's unit, the two-sided member read at `d_θ = 3`
through the theorem.  The signs are the dual exchange's, every
committed read blind to them. -/

private def yaTh : List BPair :=
  [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1]
    ++ List.replicate 3 BPair.unit

private def xbTh : List BPair :=
  List.replicate 3 BPair.unit
    ++ [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1]

/-- The nine slots joined. -/
private def cutYATh : List BPair :=
  yaTh ++ yaTh ++ yaTh ++ yaTh ++ yaTh ++ yaTh ++ yaTh ++ yaTh
    ++ yaTh

private def cutXBTh : List BPair :=
  xbTh ++ xbTh ++ xbTh ++ xbTh ++ xbTh ++ xbTh ++ xbTh ++ xbTh
    ++ xbTh

example : (dotP cutYATh cutYATh).oneValue
    (BPair.ofNat 3 * BPair.ofNat 9) := by decide +kernel

example : (dotP cutXBTh cutXBTh).oneValue
    (BPair.ofNat 3 * BPair.ofNat 9) := by decide +kernel

example : (dotP cutYATh cutXBTh).oneValue BPair.unit := by decide +kernel

/-- The member display through the theorem at the vacant
pairing. -/
example : ¬ (BPair.ofNat 3 * BPair.ofNat 9
      * (BPair.ofNat 3 * BPair.ofNat 9)
    < dotP cutYATh cutXBTh * dotP cutYATh cutXBTh) :=
  cutSq cutYATh cutXBTh rfl 3 (BPair.ofNat 9) (BPair.ofNat 9)
    (by decide +kernel) (by decide +kernel)

/-- The member window pair at the `θ`-frame: the unit state against
the trace element, the three diagonal coordinates at three copies
each. -/
private def xcTh : List BPair :=
  BPair.ofNat 3 :: List.replicate 9 BPair.unit

private def mxcTh : List BPair :=
  BPair.unit :: List.replicate 9 (BPair.ofNat 1)

example : (dotP xcTh xcTh).oneValue (BPair.ofNat 9) := by decide +kernel

/-- The coherence pin: `⟨χ_θ, χ_θ⟩ = 1` reads `9` at the
clearing. -/
example : (dotP mxcTh mxcTh).oneValue (BPair.ofNat 9) := by decide +kernel

example : BPair.unit.oneValue (dotP xcTh mxcTh) := by decide +kernel

/-- The member's two-sided form read at `d_θ = 3` through the
theorem, the cap decided at the image's gram against the squared
count. -/
example : BPair.unit ≤ BPair.ofNat 3 * BPair.ofNat 9
    ∧ BPair.unit.swap ≤ BPair.ofNat 3 * BPair.ofNat 9 :=
  cutForm xcTh mxcTh rfl 3 (BPair.ofNat 9) BPair.unit
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The orthogonality pin at `x = y = 𝟏`: the contraction is the
block orthogonality's identity instance, the slot's `ya` the one
`Ā_{ij}` coordinate at the sign `σ(ij)` and the slot's `xb` the
`(U₄)_{ji}` coordinate, disjoint frames within the slot.  Both
coordinates carry gram weight `[1:2]`, two copies each, and the
clearing `c = 2` puts every copy at `2 · [1:2] · 1 = 1`. -/

private def orthYaPos : List BPair :=
  [BPair.ofNat 1, BPair.ofNat 1, BPair.unit, BPair.unit]

private def orthYaNeg : List BPair :=
  [(BPair.ofNat 1).swap, (BPair.ofNat 1).swap, BPair.unit, BPair.unit]

private def orthXbSlot : List BPair :=
  [BPair.unit, BPair.unit, BPair.ofNat 1, BPair.ofNat 1]

private def orthYA : List BPair :=
  orthYaPos ++ orthYaNeg ++ orthYaNeg ++ orthYaPos

private def orthXB : List BPair :=
  orthXbSlot ++ orthXbSlot ++ orthXbSlot ++ orthXbSlot

/-- The joined self-pairings: `d_f · ⟨𝟏, 𝟏⟩ = 2` uncleared, `8` at
`c² = 4`, so the gram is `4` at the count `2`. -/
example : (dotP orthYA orthYA).oneValue
    (BPair.ofNat 2 * BPair.ofNat 4) := by decide +kernel

example : (dotP orthXB orthXB).oneValue
    (BPair.ofNat 2 * BPair.ofNat 4) := by decide +kernel

/-- The cross read is vacant: `⟨𝟏, χ_f⟩ = 0`, the block
orthogonality at disjoint frames. -/
example : (dotP orthYA orthXB).oneValue BPair.unit := by decide +kernel

/-- The display through the theorem at the orthogonality pin. -/
example : ¬ (BPair.ofNat 2 * BPair.ofNat 4
      * (BPair.ofNat 2 * BPair.ofNat 4)
    < dotP orthYA orthXB * dotP orthYA orthXB) :=
  cutSq orthYA orthXB rfl 2 (BPair.ofNat 4) (BPair.ofNat 4)
    (by decide +kernel) (by decide +kernel)
