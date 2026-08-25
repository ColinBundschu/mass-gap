import MassGap.Coeff
import MassGap.Kernel
/-!
The check module for `con:coeff`'s displayed identity: the
batteries re-read the squared Cauchy--Schwarz at committed
coordinate lists by kernel `decide`, the pairing's members and the
cross fold's value pinned beside it.

At `u0 = (1, 2)`, `v0 = (-1, 4)` the pairing reads `7`, the
self-pairings `5` and `17`, and the one place pair's cross square
`(1 · 4 - 2 · (-1))² = 36`: the display is `49 + 36 = 85`.  At the
three-place lists `u2 = (1, -2, 3)`, `v2 = (-1, 2, -1)` the pairing
reads `-8` against the self-pairings `14` and `6`, and the three
place pairs contribute `0`, `4` and `16`: the display is
`64 + 20 = 84`, the vanishing pair the two places already
proportional there.  `dotP_sq_le` is consumed as the theorem at
`u0`, `v0` — the order's read taken through the proof, not
decided.

The equality case is the proportional pair `up = (1, -1)`,
`vp = (2, -2)`: every cross square vanishes, so the fold reads the
sum's unit and the squared pairing reads the self-pairings'
product outright, the display's gap empty.

The length hypothesis is load-bearing for the identity and its
refusal is committed: at `u1 = (1, 1)` against the one-place
`v1 = (1)` the pairing folds to `1` and the cross fold to the
sum's unit, while the self-pairings read `2` and `1`, so the
identity's members sit at `1` and `2` — refused by the kernel.
The order's read outlives the mismatch: the folds truncate at the
shorter list and the further self-pairing members enter as
squares, so the comparison holds at the mismatched pair too, the
committed instance beside the refusal — the corollary's
hypothesis is the identity route's frame.
-/

open ground elim coeff

private def u0 : List BPair := [⟨2, 1⟩, ⟨3, 1⟩]

private def v0 : List BPair := [⟨1, 2⟩, ⟨5, 1⟩]

private def u1 : List BPair := [⟨2, 1⟩, ⟨2, 1⟩]

private def v1 : List BPair := [⟨2, 1⟩]

private def u2 : List BPair := [⟨2, 1⟩, ⟨1, 3⟩, ⟨4, 1⟩]

private def v2 : List BPair := [⟨1, 2⟩, ⟨3, 1⟩, ⟨1, 2⟩]

private def up : List BPair := [⟨2, 1⟩, ⟨1, 2⟩]

private def vp : List BPair := [⟨3, 1⟩, ⟨1, 3⟩]

/-! The two-place list pair: the pairing, the self-pairings and
the cross fold each read their value, and the display joins
them. -/

example : (dotP u0 v0).oneValue (BPair.ofNat 7) := by decide +kernel

example : (dotP u0 u0).oneValue (BPair.ofNat 5) := by decide +kernel

example : (dotP v0 v0).oneValue (BPair.ofNat 17) := by decide +kernel

example : (crossSq u0 v0).oneValue (BPair.ofNat 36) := by decide +kernel

example : (dotP u0 v0 * dotP u0 v0 + crossSq u0 v0).oneValue
    (dotP u0 u0 * dotP v0 v0) := by decide +kernel

/-! The three-place list pair: three place pairs enter the cross
fold, one of them vacant. -/

example : (crossSq u2 v2).oneValue (BPair.ofNat 20) := by decide +kernel

example : (dotP u2 v2 * dotP u2 v2 + crossSq u2 v2).oneValue
    (dotP u2 u2 * dotP v2 v2) := by decide +kernel

/-! The order's read taken through the theorem, the hypothesis the
lists' own length read. -/

example : ¬ (dotP u0 u0 * dotP v0 v0 < dotP u0 v0 * dotP u0 v0) :=
  coeff.dotP_sq_le u0 v0 rfl

example : ¬ (dotP u2 u2 * dotP v2 v2 < dotP u2 v2 * dotP u2 v2) :=
  coeff.dotP_sq_le u2 v2 rfl

/-! The equality case at proportional lists: the cross fold reads
the sum's unit and the squared pairing reads the product. -/

example : (crossSq up vp).oneValue BPair.unit := by decide +kernel

example : (dotP up vp * dotP up vp).oneValue
    (dotP up up * dotP vp vp) := by decide +kernel

example : (dotP up vp * dotP up vp + crossSq up vp).oneValue
    (dotP up up * dotP vp vp) := by decide +kernel

/-! The length hypothesis is load-bearing: at mismatched lists the
identity's members stand apart, the pairing's fold stopping at the
shorter list while the self-pairings read their own. -/

example : (dotP u1 v1 * dotP u1 v1 + crossSq u1 v1).oneValue
    (BPair.ofNat 1) := by decide +kernel

example : (dotP u1 u1 * dotP v1 v1).oneValue (BPair.ofNat 2) := by
  decide +kernel

example : ¬ (dotP u1 u1 * dotP v1 v1
    < dotP u1 v1 * dotP u1 v1) := by decide +kernel

example : ¬ (dotP u1 v1 * dotP u1 v1 + crossSq u1 v1).oneValue
    (dotP u1 u1 * dotP v1 v1) := by decide +kernel

/-! The member cap's instance reads at the presentation Gram
(`lem:loopcap`'s member clause at `con:coeff`'s pairing;
`thm:truncation`'s member cap the consumer).  The window is the
unit state with the adjoint character's state, every state on the
four-factor site `(U, U†, U, U†)`: the unit is
`[1 : d_f²] tr(UU†)²` at the wiring `[1,0,3,2]`, the character
state `[1 : d_f] tr U tr U† tr(UU†)` at `[0,1,3,2]`, and the
magnetic images multiply the two-factor spellings by
`χ_adj = tr U tr U† - 1`, the pair's presentation.  The entries
are the direct tier's at-residue pairings (`kernel.pairAt`) folded
over the combination terms at evaluated coefficients (`pairEv`,
the accumulating pair at the products' clearing), each entry
pinned cleared against its committed count: the Gram
`[[1, 1], [1, 2]]` at both counts, the form `[[0, 1], [1, 3]]` at
the count two against `[[0, 1], [1, 4]]` at three, and the
squared-image Gram `[[1, 2], [2, 6]]` against `[[1, 3], [3, 13]]`.
The three cap comparisons assemble from the committed counts —
`d_θ G - F` and `d_θ G + F`, the term two-sided at the adjoint
dimension, with `d_θ² G - G_M`, the multiplication's square — and
each is positive semidefinite at its committed split, the diagonal
congruence `T = [[1, -b], [0, a]]` per matrix; the forged scale,
the two-sided read at one in place of `d_θ`, refuses at a
lower-side block, the cap's scale the load-bearing datum. -/

private def cF4 : states.FList :=
  [(false, false), (false, true), (false, false), (false, true)]

private def pairEv (F : states.FList)
    (c1 c2 : List (List Nat × BPair × BPair)) (rv : Nat) :
    BPair × BPair :=
  c1.foldl (fun acc e1 =>
    c2.foldl (fun acc2 e2 =>
      let n := (e1.2.1 * e2.2.1
        * ((kernel.pairAt F e1.1 e2.1 rv).getD BPair.unit)).norm
      let d := (e1.2.2 * e2.2.2).norm
      ground.cpAdd acc2 (n, d)) acc)
    (BPair.unit, BPair.ofNat 1)

/-- The cleared entry read: the fold's first member against the
committed count's multiple of its second. -/
private def entryAt (F : states.FList)
    (c1 c2 : List (List Nat × BPair × BPair)) (rv v : Nat) : Prop :=
  let p := pairEv F c1 c2 rv
  p.1.oneValue (BPair.ofNat v * p.2)

private instance (F : states.FList)
    (c1 c2 : List (List Nat × BPair × BPair)) (rv v : Nat) :
    Decidable (entryAt F c1 c2 rv v) :=
  inferInstanceAs (Decidable (BPair.oneValue _ _))

private def one1 : BPair := BPair.ofNat 1

private def uS (rv : Nat) : List (List Nat × BPair × BPair) :=
  [([1, 0, 3, 2], one1, BPair.ofNat (rv * rv))]
private def pS (rv : Nat) : List (List Nat × BPair × BPair) :=
  [([0, 1, 3, 2], one1, BPair.ofNat rv)]
private def muS (rv : Nat) : List (List Nat × BPair × BPair) :=
  [([1, 0, 2, 3], one1, BPair.ofNat rv),
   ([1, 0, 3, 2], ⟨1, 2⟩, BPair.ofNat (rv * rv))]
private def mpS (rv : Nat) : List (List Nat × BPair × BPair) :=
  [([0, 1, 2, 3], one1, one1),
   ([0, 1, 3, 2], ⟨1, 2⟩, BPair.ofNat rv)]

/-! The Gram's entries at both counts. -/

example : entryAt cF4 (uS 2) (uS 2) 2 1 := by decide +kernel
example : entryAt cF4 (uS 2) (pS 2) 2 1 := by decide +kernel
example : entryAt cF4 (pS 2) (pS 2) 2 2 := by decide +kernel
example : entryAt cF4 (uS 3) (uS 3) 3 1 := by decide +kernel
example : entryAt cF4 (uS 3) (pS 3) 3 1 := by decide +kernel
example : entryAt cF4 (pS 3) (pS 3) 3 2 := by decide +kernel

/-! The form's entries: the count two's last read `3` against the
count three's `4`, the residue's own move. -/

example : entryAt cF4 (uS 2) (muS 2) 2 0 := by decide +kernel
example : entryAt cF4 (uS 2) (mpS 2) 2 1 := by decide +kernel
example : entryAt cF4 (pS 2) (muS 2) 2 1 := by decide +kernel
example : entryAt cF4 (pS 2) (mpS 2) 2 3 := by decide +kernel
example : entryAt cF4 (uS 3) (muS 3) 3 0 := by decide +kernel
example : entryAt cF4 (uS 3) (mpS 3) 3 1 := by decide +kernel
example : entryAt cF4 (pS 3) (muS 3) 3 1 := by decide +kernel
example : entryAt cF4 (pS 3) (mpS 3) 3 4 := by decide +kernel

/-! The squared-image Gram's entries. -/

example : entryAt cF4 (muS 2) (muS 2) 2 1 := by decide +kernel
example : entryAt cF4 (muS 2) (mpS 2) 2 2 := by decide +kernel
example : entryAt cF4 (mpS 2) (mpS 2) 2 6 := by decide +kernel
example : entryAt cF4 (muS 3) (muS 3) 3 1 := by decide +kernel
example : entryAt cF4 (muS 3) (mpS 3) 3 3 := by decide +kernel
example : entryAt cF4 (mpS 3) (mpS 3) 3 13 := by decide +kernel

/-! The cap comparisons at the committed counts, each positive
semidefinite at its split: at the count two, `d_θ = 3`,
`3G - F = [[3, 2], [2, 3]]`, `3G + F = [[3, 4], [4, 9]]` and
`9G - G_M = [[8, 7], [7, 12]]`; at three, `d_θ = 8`,
`8G - F = [[8, 7], [7, 12]]`, `8G + F = [[8, 9], [9, 20]]` and
`64G - G_M = [[63, 61], [61, 115]]`. -/

private def capA2 : elim.Mat := [[⟨4, 1⟩, ⟨3, 1⟩], [⟨3, 1⟩, ⟨4, 1⟩]]
private def spA2 : inertia.Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 3⟩], [⟨1, 1⟩, ⟨4, 1⟩]], rfl⟩,
   ⟨[[⟨4, 1⟩, ⟨3, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨4, 1⟩, .one ⟨16, 1⟩], 0, rfl⟩

private def capB2 : elim.Mat := [[⟨4, 1⟩, ⟨5, 1⟩], [⟨5, 1⟩, ⟨10, 1⟩]]
private def spB2 : inertia.Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 5⟩], [⟨1, 1⟩, ⟨4, 1⟩]], rfl⟩,
   ⟨[[⟨4, 1⟩, ⟨5, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨4, 1⟩, .one ⟨34, 1⟩], 0, rfl⟩

private def capW : elim.Mat := [[⟨9, 1⟩, ⟨8, 1⟩], [⟨8, 1⟩, ⟨13, 1⟩]]
private def spW : inertia.Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 8⟩], [⟨1, 1⟩, ⟨9, 1⟩]], rfl⟩,
   ⟨[[⟨9, 1⟩, ⟨8, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨9, 1⟩, .one ⟨377, 1⟩], 0, rfl⟩

private def capB3 : elim.Mat := [[⟨9, 1⟩, ⟨10, 1⟩], [⟨10, 1⟩, ⟨21, 1⟩]]
private def spB3 : inertia.Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 10⟩], [⟨1, 1⟩, ⟨9, 1⟩]], rfl⟩,
   ⟨[[⟨9, 1⟩, ⟨10, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨9, 1⟩, .one ⟨633, 1⟩], 0, rfl⟩

private def capC3 : elim.Mat :=
  [[⟨64, 1⟩, ⟨62, 1⟩], [⟨62, 1⟩, ⟨116, 1⟩]]
private def spC3 : inertia.Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 62⟩], [⟨1, 1⟩, ⟨64, 1⟩]], rfl⟩,
   ⟨[[⟨64, 1⟩, ⟨62, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨64, 1⟩, .one ⟨222013, 1⟩], 0, rfl⟩

example : inertia.splitRead capA2 spA2 := by decide +kernel
example : inertia.psdAt spA2 := by decide +kernel
example : inertia.splitRead capB2 spB2 := by decide +kernel
example : inertia.psdAt spB2 := by decide +kernel
example : inertia.splitRead capW spW := by decide +kernel
example : inertia.psdAt spW := by decide +kernel
example : inertia.splitRead capB3 spB3 := by decide +kernel
example : inertia.psdAt spB3 := by decide +kernel
example : inertia.splitRead capC3 spC3 := by decide +kernel
example : inertia.psdAt spC3 := by decide +kernel

/-! The forged scale's refusal: the two-sided read at one in place
of `d_θ` at the count two, `G - F = [[1, 0], [0, -1]]`, one
lower-side block — the cap's scale load-bearing. -/

private def capForge : elim.Mat := [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨1, 2⟩]]
private def spForge : inertia.Split 2 :=
  ⟨⟨inertia.idMat 2, rfl⟩, ⟨inertia.idMat 2, rfl⟩,
   [.one ⟨2, 1⟩, .one ⟨1, 2⟩], 0, rfl⟩

example : inertia.splitRead capForge spForge := by decide +kernel
example : inertia.revAt spForge = 1 := by decide +kernel
