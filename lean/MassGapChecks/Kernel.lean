import MassGap.Kernel
/-!
The check module for `rem:kernel`: the batteries re-read the word
index by kernel `decide`.  The canonical rotation; the word
multisets at the four-factor list `[U, U, U†, U†]` — the two
pairings at exchanged repeated positions one state, the gauge
read, against the four-cycle's refusal; the combination equality
at the word keys with the coefficient refusal and the
zero-second-member refusal (the pairs' site read); the kernel
read's refusals at the three forged shapes — a zero second
member, a vector at the sum's unit at the residue with occupied
symbols, and a duplicated key — beside the off-kernel refusal at
`[U, U†]` (the Gram `[[2, d], [d, d²]]`, the claimed `(d, -1)`
folding to `d`); and the domain guard's committed record at the
three-box antisymmetrizer, `(tr U)³ - 3 tr U tr U² + 2 tr U³` at
`d_f = 2` over the three distinct-word wirings: the residue sits
at or below the clearance radius (three boxes against the count
two, the span dependent, the shared Weingarten determinant
reading the sum's unit there), so the symbolic checker REFUSES it
at the radius comparison — the boundary where the unguarded fold
had read equal members at every vector whatever — and the
instance sits with the direct tag, the emitted gate's records the
deeper lists'.  The off-kernel refusal reads at a residue beyond
the radius, where the comparison admits and the fold
discriminates.

The direct tag's tier closes that recorded pair: `charAt` at the
classical `S₂` and `S₃` tables; `pairAt` at the six-value
at-residue Gram of the three-box wirings at `d_f = 2`
(`⟨p111, p111⟩ = 5` through `⟨p3, p3⟩ = 2`) with the coherence pin
at `d_f = 4` tying the direct read to the symbolic pairing's
Horner evaluation; the mixed-dagger and
null-cycle pins at `d_f = 2` (`|tr U|⁴` at two, `tr(U U†)²` at
four, the four-factor diagonal at fourteen, the crossing wiring's
refusal the `Option`'s own); and `directRead`, the at-residue
Gram's row read, at the six-wiring antisymmetrizer itself — the
committed refusal above keeps the symbolic checker's boundary,
and the positive member reads at `d_f = 1` and `d_f = 2` sit
beside it at last, the row read's completeness uniform in the
residue with the one-variable window's own instance included,
with the off-member refusal at `d_f = 3` reading the identity
generator's row at six — and at the relation members beyond the
daggerless site: `4 |det U|² - d_f²` on four factors and the
tied-degree member on `[U, U, U†]`, each accepted at `d_f = 2`
and refused at `d_f = 3`, the second the refuter of any
per-degree shape-fold spelling; the occupancy refusal beside
them, a coefficient whose second member reaches the unit at the
residue.  The factor-list guard refuses a cross-variable site
(`tr(U V)`) at either tag, and `memberAt` branches at the radius:
the antisymmetrizer's direct branch at `d_f = 2`, the symbolic
branch at `d_f = 5` on `con:res`'s adjoint-site instances.  The
module's cost is the coherence pin's two symbolic `wg.pairPhi`
reads at the six-factor site, the `padj (gramWg 3)` adjugate under
kernel reduction. -/
set_option maxHeartbeats 16000000

open ground poly genericlift states kernel

private def f4 : FList :=
  [(false, false), (false, false), (false, true), (false, true)]
private def f2 : FList := [(false, false), (false, true)]
private def f3 : FList :=
  [(false, false), (false, false), (false, false)]

/-! The canonical rotation, and the word multisets at
`[U, U, U†, U†]`: exchanged repeated positions one state. -/

example : canonRot [2, 0, 1] = [0, 1, 2] := by decide +kernel
example : wordsOf f4 [2, 3, 0, 1] = [[0, 1], [0, 1]] := by decide +kernel
example : oneState f4 [2, 3, 0, 1] [3, 2, 1, 0] := by decide +kernel
example : ¬ oneState f4 [2, 3, 0, 1] [1, 2, 3, 0] := by decide +kernel

/-! The combination equality at the word keys: the gauge pair one
state at every coefficient, the doubled coefficient and the zero
second member refused. -/

example : combEqRead f4 [([2, 3, 0, 1], pOne)]
    [([3, 2, 1, 0], pOne)] := by decide +kernel
example : ¬ combEqRead f4 [([2, 3, 0, 1], pOne)]
    [([3, 2, 1, 0], ([⟨3, 1⟩], [⟨2, 1⟩]))] := by decide +kernel
example : ¬ combEqRead [(false, false)]
    [([0], ([⟨2, 1⟩], [])), ([0], ([⟨2, 1⟩], []))]
    [([0], ([⟨6, 1⟩], [⟨2, 1⟩]))] := by decide +kernel

/-! The kernel read's refusals: the three forged shapes and the
off-kernel vector. -/

example : ¬ kernelRead f2 [[0, 1], [1, 0]]
    [(poly.one, []), (poly.one, [])]
    ⟨4, 1⟩ := by decide +kernel
example : ¬ kernelRead f2 [[0, 1], [1, 0]]
    [([⟨1, 2⟩, ⟨2, 1⟩], [⟨2, 1⟩]), ([⟨1, 2⟩, ⟨2, 1⟩], [⟨2, 1⟩])]
    ⟨4, 1⟩ := by decide +kernel
example : ¬ kernelRead
    [(false, false), (false, false)] [[0, 1], [0, 1]]
    [([⟨2, 1⟩], [⟨2, 1⟩]), ([⟨1, 2⟩], [⟨2, 1⟩])] ⟨4, 1⟩ := by decide +kernel
example : ¬ kernelRead f2 [[0, 1], [1, 0]]
    [([⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩]), ([⟨1, 2⟩], [⟨2, 1⟩])]
    ⟨4, 1⟩ := by decide +kernel

/-! The domain guard at the three-box antisymmetrizer: `d_f = 2`
sits at or below the clearance radius (the three-permutation span
dependent, the shared determinant vanishing), so the symbolic
checker refuses the record — its genuine null-ness is the direct
tag's, the read here the boundary's own committed pin. -/

example : ¬ kernelRead f3 [[0, 1, 2], [1, 0, 2], [1, 2, 0]]
    [([⟨2, 1⟩], [⟨2, 1⟩]), ([⟨1, 4⟩], [⟨2, 1⟩]),
     ([⟨3, 1⟩], [⟨2, 1⟩])] ⟨2, 1⟩ := by decide +kernel

/-! The character read at the classical tables: `S₂` and `S₃` at
three variables, the shapes as row lists against the cycle
types. -/

example : (charAt 3 [2] [1, 1]).oneValue (BPair.ofNat 1) := by decide +kernel
example : (charAt 3 [2] [2]).oneValue (BPair.ofNat 1) := by decide +kernel
example : (charAt 3 [1, 1] [1, 1]).oneValue (BPair.ofNat 1) := by
  decide +kernel
example : (charAt 3 [1, 1] [2]).oneValue ((BPair.ofNat 1).swap) := by
  decide +kernel

example : (charAt 3 [3] [1, 1, 1]).oneValue (BPair.ofNat 1) := by
  decide +kernel
example : (charAt 3 [3] [2, 1]).oneValue (BPair.ofNat 1) := by decide +kernel
example : (charAt 3 [3] [3]).oneValue (BPair.ofNat 1) := by decide +kernel
example : (charAt 3 [2, 1] [1, 1, 1]).oneValue (BPair.ofNat 2) := by
  decide +kernel
example : (charAt 3 [2, 1] [2, 1]).oneValue BPair.unit := by decide +kernel
example : (charAt 3 [2, 1] [3]).oneValue ((BPair.ofNat 1).swap) := by
  decide +kernel
example : (charAt 3 [1, 1, 1] [1, 1, 1]).oneValue (BPair.ofNat 1) := by
  decide +kernel
example : (charAt 3 [1, 1, 1] [2, 1]).oneValue
    ((BPair.ofNat 1).swap) := by decide +kernel
example : (charAt 3 [1, 1, 1] [3]).oneValue (BPair.ofNat 1) := by
  decide +kernel

/-! The at-residue pairing at the three-box wirings and `d_f = 2`,
the six-value Gram whose singularity the committed refusal above
records; and the coherence pin at `d_f = 4`, the direct read
against the symbolic pairing's Horner evaluation. -/

example : ((pairAt f3 [0, 1, 2] [0, 1, 2] 2).getD BPair.unit).oneValue
    (BPair.ofNat 5) := by decide +kernel
example : ((pairAt f3 [0, 1, 2] [1, 0, 2] 2).getD BPair.unit).oneValue
    (BPair.ofNat 1) := by decide +kernel
example : ((pairAt f3 [0, 1, 2] [1, 2, 0] 2).getD BPair.unit).oneValue
    ((BPair.ofNat 1).swap) := by decide +kernel
example : ((pairAt f3 [1, 0, 2] [1, 0, 2] 2).getD BPair.unit).oneValue
    (BPair.ofNat 1) := by decide +kernel
example : ((pairAt f3 [1, 0, 2] [1, 2, 0] 2).getD BPair.unit).oneValue
    (BPair.ofNat 1) := by decide +kernel
example : ((pairAt f3 [1, 2, 0] [1, 2, 0] 2).getD BPair.unit).oneValue
    (BPair.ofNat 2) := by decide +kernel

example : BPair.oneValue
    (poly.eval (wg.pairPhi f3 f3 [0, 1, 2] [0, 1, 2]).1
      (BPair.ofNat 4))
    ((pairAt f3 [0, 1, 2] [0, 1, 2] 4).getD BPair.unit
      * poly.eval (wg.pairPhi f3 f3 [0, 1, 2] [0, 1, 2]).2
        (BPair.ofNat 4)) := by decide +kernel

/-! The mixed-dagger and null-cycle paths at `d_f = 2`: the
conjugation's role assignment and the residue scalar, each read at
its own pin — `|tr U|⁴` at two, the pure null-cycle square
`tr(U U†)²` at four, and the four-factor site's diagonal and
mixed entries — with the crossing wiring's refusal the `Option`'s
own. -/

example : ((pairAt f2 [0, 1] [0, 1] 2).getD BPair.unit).oneValue
    (BPair.ofNat 2) := by decide +kernel
example : ((pairAt f2 [1, 0] [1, 0] 2).getD BPair.unit).oneValue
    (BPair.ofNat 4) := by decide +kernel
example : ((pairAt f4 [0, 1, 2, 3] [0, 1, 2, 3] 2).getD
    BPair.unit).oneValue (BPair.ofNat 14) := by decide +kernel
example : ((pairAt f4 [1, 0, 2, 3] [0, 1, 3, 2] 2).getD
    BPair.unit).oneValue (BPair.ofNat 2) := by decide +kernel
example : pairAt [(false, false), (true, false)] [1, 0] [1, 0] 2
    = none := by decide +kernel

/-! The landing site's closure: the six-wiring antisymmetrizer is
the at-residue member at `d_f = 2` — the direct read the committed
refusal's other half — and off the member at `d_f = 3`, the
identity generator's row reading six.  The factor-list guard
refuses the cross-variable site `tr(U V)` at either tag. -/

/-- The three-box antisymmetrizer,
`(tr U)³ - 3 tr U tr U² + 2 tr U³` as the six wirings of `S₃` at
the sign coefficients. -/
private def aSym : Comb :=
  [([0, 1, 2], pOne), ([1, 0, 2], ([⟨1, 2⟩], [⟨2, 1⟩])),
   ([0, 2, 1], ([⟨1, 2⟩], [⟨2, 1⟩])),
   ([2, 1, 0], ([⟨1, 2⟩], [⟨2, 1⟩])),
   ([1, 2, 0], pOne), ([2, 0, 1], pOne)]

example : directRead f3 aSym 1 := by decide +kernel
example : directRead f3 aSym 2 := by decide +kernel
example : ¬ directRead f3 aSym 3 := by decide +kernel

private def fUV : FList := [(false, false), (true, false)]

example : ¬ directRead fUV [([1, 0], pOne)] 2 := by decide +kernel
example : ¬ directRead fUV [([1, 0], pOne)] 5 := by decide +kernel

/-! The relation members beyond the daggerless site, the row
read's own reach: `4 |det U|² - d_f²` on `[U, U, U†, U†]` and
`(tr U)² tr U† - tr U² tr U† - tr U tr(U U†)` on `[U, U, U†]`,
each the null function at `d_f = 2` — the member read accepts —
and off it at `d_f = 3`, the refusals beside; the second member's
null-cycle term ties the degree grid, the shape-fold spelling's
own refuter.  The occupancy refusal beside them: a coefficient
whose second member reaches the unit at the residue sits off the
read. -/

private def cDet : Comb :=
  [([0, 1, 2, 3], pOne), ([0, 1, 3, 2], ([⟨1, 2⟩], [⟨2, 1⟩])),
   ([1, 0, 2, 3], ([⟨1, 2⟩], [⟨2, 1⟩])), ([1, 0, 3, 2], pOne),
   ([2, 3, 0, 1], ([⟨1, 2⟩], [⟨2, 1⟩]))]

private def f21 : FList :=
  [(false, false), (false, false), (false, true)]

private def cTie : Comb :=
  [([0, 1, 2], pOne), ([1, 0, 2], ([⟨1, 2⟩], [⟨2, 1⟩])),
   ([0, 2, 1], ([⟨1, 2⟩], [⟨2, 1⟩]))]

example : directRead f4 cDet 2 := by decide +kernel
example : ¬ directRead f4 cDet 3 := by decide +kernel
example : directRead f21 cTie 2 := by decide +kernel
example : ¬ directRead f21 cTie 3 := by decide +kernel
example : ¬ directRead f3
    [([0, 1, 2], ([⟨1, 3⟩, ⟨2, 1⟩], [⟨1, 3⟩, ⟨2, 1⟩])),
     ([0, 1, 2], pOne)] 2 := by decide +kernel

/-! The tag branch: the antisymmetrizer's direct branch at
`d_f = 2`, and the symbolic branch at `d_f = 5` on `con:res`'s
adjoint-site instances — the vacant member against the occupied
`|tr U|²`. -/

example : memberAt f3 aSym 2 := by decide +kernel
example : memberAt f2 ([] : Comb) 5 := by decide +kernel
example : ¬ memberAt f2 [([0, 1], pOne)] 5 := by decide +kernel
