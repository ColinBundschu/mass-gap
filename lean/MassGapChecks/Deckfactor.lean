import MassGap.Deckfactor
/-!
The check module for `lem:deckfactor`: the batteries re-read the
deck symbol and the interior factor by kernel `decide`.  The
symmetric `p = 6z⁴ - 35z³ + 62z² - 35z + 6 = (2z²-5z+2)(3z²-10z+3)`
— the symmetry read with the asymmetric refusal, the
back-substituted symbol `6w² - 35w + 50 = (2w-5)(3w-10)`, the
assembly coherence, and the interior--exterior factorization at the
root pairs `(1/2, 2)` and `(1/3, 3)` with the forged-pair refusal.
The band read at the symbol `(w-3)(w-4)` — every root off the
closed crossing segment `[-2, 2]`, `H₁` positive definite with the
pencil at `diag(17, 1020)`; the cleared-variable display at the
walk's symbol `2w - 5`, the monic `y - 5` at the doubled
magnitude's endpoints with the root outside, against `2w - 3`'s
cleared root inside at the count one, the lower-side tops' swapped
displays, and the vanishing top's collapsed endpoints refusing.
The walk's chord instance at base two,
`z* = 1/2` at `w = 5/2` — the interior member with the exterior
refusal, and the margin's `[9 : 4]` crossing square. -/
set_option maxHeartbeats 4000000

open ground poly elim inertia deckfactor

/-! The deck-symmetric `p = (2z²-5z+2)(3z²-10z+3)` at `m = 2`: the
symmetry, the symbol, the assembly, and the factorization. -/

private def pD : Poly := [⟨7, 1⟩, ⟨1, 36⟩, ⟨63, 1⟩, ⟨1, 36⟩, ⟨7, 1⟩]

example : deckSymRead pD 2 := by decide +kernel

/-! The deck read at the value: a trailing unit coefficient rides
beyond the doubled degree and the read sees the value's own
symmetry. -/

example : deckSymRead
    [⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩] 2 := by decide +kernel

example : ¬ deckSymRead [⟨2, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] 2 := by
  decide +kernel
example : poly.oneValue (symbolOf pD 2) [⟨51, 1⟩, ⟨1, 36⟩, ⟨7, 1⟩] := by
  decide +kernel
example : symbolRead pD 2 := by decide +kernel
example : intExtRead pD ⟨7, 1⟩
    [(⟨2, 1⟩, ⟨5, 1⟩, 2), (⟨2, 1⟩, ⟨10, 1⟩, 3)] := by decide +kernel
example : ¬ intExtRead pD ⟨7, 1⟩
    [(⟨2, 1⟩, ⟨5, 1⟩, 2), (⟨3, 1⟩, ⟨10, 1⟩, 3)] := by decide +kernel

/-! The band read at the display `(w-3)(w-4) = w² - 7w + 12`: the
monic clearing its own below-top list at the unit magnitude, every
root off the closed crossing segment. -/

private def sB : Poly := [⟨13, 1⟩, ⟨1, 8⟩, ⟨2, 1⟩]
private def spH34 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 8⟩], [⟨1, 1⟩, ⟨3, 1⟩]], rfl⟩,
   ⟨[[⟨3, 1⟩, ⟨8, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨3, 1⟩, .one ⟨3, 1⟩], 0, rfl⟩
private def spB34 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 64⟩], [⟨1, 1⟩, ⟨18, 1⟩]], rfl⟩,
   ⟨[[⟨18, 1⟩, ⟨64, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨18, 1⟩, .one ⟨1021, 1⟩], 0, rfl⟩

example : bandClear sB spH34 spB34 := by decide +kernel

/-! The walk's chord instance at base two: the interior member
`z* = 1/2` at `w = 5/2`, the exterior partner's refusal, and the
margin's crossing square `9 = 1 · 9`, the `[9 : 4]` read. -/

example : interiorRead ⟨2, 1⟩ ⟨6, 1⟩ 2 := by decide +kernel
example : ¬ interiorRead ⟨5, 1⟩ ⟨6, 1⟩ 2 := by decide +kernel
example : marginRead ⟨2, 1⟩ ⟨6, 1⟩ 2 := by decide +kernel
example : marginRead ⟨2, 1⟩ ⟨3, 1⟩ 1 := by decide +kernel

/-! The cleared-variable display at the walk's symbol `2w - 5`: the
below-top list reads `-5` (the monic `y - 5` at `y = 2w`), the
segment count at the doubled magnitude's endpoints `(-4, 4)` reads
the root `5` outside, and at the symbol `2w - 3` the cleared root
`3` sits inside, the count one with the vacancy's refusal. -/

private def spOne (a : BPair) : Split 1 :=
  ⟨⟨inertia.idMat 1, rfl⟩, ⟨inertia.idMat 1, rfl⟩,
   [.one a], 0, rfl⟩

example : poly.oneValue (clearVarBT [⟨1, 6⟩, ⟨3, 1⟩]) [⟨1, 6⟩] := by
  decide +kernel
example : bandClear [⟨1, 6⟩, ⟨3, 1⟩] (spOne ⟨2, 1⟩)
    (spOne ⟨10, 1⟩) := by decide +kernel
example : hermitesign.segCountRead (clearVarBT [⟨1, 4⟩, ⟨3, 1⟩])
    ⟨2, 6⟩ ⟨6, 2⟩ 1 1 (spOne ⟨2, 1⟩) (spOne ⟨1, 8⟩) := by decide +kernel
example : ¬ bandClear [⟨1, 4⟩, ⟨3, 1⟩] (spOne ⟨2, 1⟩)
    (spOne ⟨1, 8⟩) := by decide +kernel

/-! The sign normalization: a lower-side top swaps the members —
`-2w - 3` clears to `y + 3` and `-2w² + 3w + 2` to
`y² - 3y - 4`, one display per case — and a vanishing top
collapses the endpoints, the ordered-endpoint read refusing. -/

example : poly.oneValue (clearVarBT [⟨1, 4⟩, ⟨1, 3⟩]) [⟨4, 1⟩] := by
  decide +kernel
example : poly.oneValue (clearVarBT [⟨3, 1⟩, ⟨4, 1⟩, ⟨1, 3⟩])
    [⟨1, 5⟩, ⟨1, 4⟩] := by decide +kernel
example : ¬ bandClear [⟨3, 1⟩, ⟨1, 1⟩] (spOne ⟨2, 1⟩)
    (spOne ⟨2, 1⟩) := by decide +kernel
