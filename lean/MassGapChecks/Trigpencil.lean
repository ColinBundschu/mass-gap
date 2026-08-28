import MassGap.Trigpencil
/-!
The check module for `thm:trigpencil`: the batteries decide the
theorem's three reads at one committed fiber pencil.  The pencil is
the order-two symmetric matrix carrying `lem:deckfactor`'s own
assembled deck-symmetric polynomial on the diagonal — the symbol of
`P_3` assembled at half-degree one, `z² + z + 1` — with the chord
monomial off it, the shape a separation's block against the
reversed separation's transpose.  Its determinant is the fiber
symbol, degree four and palindromic at half-degree two, so the
symbol read, the per-grade degree bound and the deck symmetry all
land on the one object.

The refusals isolate each read: the symbol read refuses at a degree
below its own, the grade bound refuses at a grade whose bound the
diagonal entry exceeds, and the deck symmetry refuses at the
pencil with one off-diagonal entry emptied — a pencil whose
determinant is still deck-symmetric, so what the refusal catches is
the pencil's own symmetry rather than the symbol's.

The two-variable tier reads at the same committed pencil: the
level pair's site datum over it at the unit chord gram, the symbol
at `symbolAt`'s display with three refusals, the boundary
coefficients against the one-variable minors, and the evaluation
coherence at a stated level point with a forged point refusing.
-/

open ground elim

/-! The committed fiber pencil: `lem:deckfactor`'s assembled symbol
on the diagonal, the chord monomial off it. -/

private def symA : poly.Poly := deckfactor.assembleSym (deck.pSum 1) 1
private def zP : poly.Poly := [BPair.unit, BPair.ofPos Pos.one]
private def fibS : split.PMat := [[symA, zP], [zP, symA]]

/-! The diagonal entry is the deck-symmetric assembly at half-degree
one, `lem:deckfactor`'s coherence its own read. -/

example : deckfactor.symbolRead symA 1 := by decide +kernel
example : deckfactor.deckSymRead symA 1 := by decide +kernel

/-! The theorem's three reads at the pencil. -/

example : trigpencil.symbolRead fibS 4 := by decide +kernel
example : trigpencil.gradeBoundRead fibS [2, 2] := by decide +kernel
example : trigpencil.deckSymmetryRead fibS 2 2 := by decide +kernel

/-! The refusals. -/

example : ¬ trigpencil.symbolRead fibS 3 := by decide +kernel
example : ¬ trigpencil.gradeBoundRead fibS [1, 2] := by decide +kernel
example : ¬ trigpencil.deckSymmetryRead [[symA, zP], [[], symA]] 2 2 := by
  decide +kernel

/-! The refused pencil's own determinant stays deck-symmetric: the
symmetry the read catches is the pencil's, not the symbol's. -/

example : deckfactor.deckSymRead (split.pminor [[symA, zP], [[], symA]]) 2 := by
  decide +kernel

/-! The two-variable symbol at the committed pencil: the level
pair's site datum over the chord-entried pencil at the unit chord
gram, its symbol at outer degree two and inner bound four with the
three refusals — a wrong outer degree, a wrong inner bound, and
the site datum at the vacant gram, whose leading coefficient sits
at the sum's unit. -/

private def pId : split.PMat := [[poly.one, []], [[], poly.one]]
private def Z2 : split.PPMat := split.ppzMat fibS pId

example : trigpencil.symbolAt Z2 2 4 := by decide +kernel
example : ¬ trigpencil.symbolAt Z2 1 4 := by decide +kernel
example : ¬ trigpencil.symbolAt Z2 2 3 := by decide +kernel
example : ¬ trigpencil.symbolAt
    (split.ppzMat fibS [[[], []], [[], []]]) 2 4 := by decide +kernel

/-! The symbol's boundary coefficients read the one-variable
minors: the constant reads the chord pencil's own determinant at
the even order, and the leading reads the gram's. -/

example : poly.oneValue (ground.getAt [] (split.ppminor Z2) 0)
    (split.pminor fibS) := by decide +kernel
example : poly.oneValue (ground.getAt [] (split.ppminor Z2) 2)
    (split.pminor pId) := by decide +kernel

/-! The evaluation coherence at a stated level point: the outer
evaluation of the symbol reads one value with the minor of the
entrywise evaluated pencil, and a forged point refuses. -/

private def lnPt : BPair := BPair.ofNat 3
private def evZ : split.PMat :=
  Z2.map (fun r => r.map (fun P => poly.pevalC P [lnPt] 2 1))

example : poly.oneValue (poly.pevalC (split.ppminor Z2) [lnPt] 2 2)
    (split.pminor evZ) := by decide +kernel
example : ¬ poly.oneValue
    (poly.pevalC (split.ppminor Z2) [BPair.ofNat 5] 2 2)
    (split.pminor evZ) := by decide +kernel

/-! The display reads the value: at a leading-key cancellation the
fold's output list keeps its length while the degree drops, and
the read sees the degree — the pencil below has determinant the
balance read of `z²` against `(1+z)²`, degree one at a
length-three fold output.  The fold branch reads beside it at a
list off the square frame, where the walk and the fold genuinely
part: the ragged pencil's fold reads degree two while the walk's
value sits at degree one, so the passing pin is the fold branch's
own record.  The two-variable display and the grade bound read
their values as well: an outer trailing unit coefficient and an
in-bound entry of trailing units each read at the value. -/

private def zOne : poly.Poly :=
  [BPair.ofPos Pos.one, BPair.ofPos Pos.one]
private def cancS : split.PMat := [[zP, zOne], [zOne, zP]]

example : trigpencil.symbolRead cancS 1 := by decide +kernel
example : ¬ trigpencil.symbolRead cancS 2 := by decide +kernel

example : trigpencil.symbolRead
    [[zP, zOne, zP], [zOne, zP, zOne]] 2 := by decide +kernel
example : ¬ trigpencil.symbolRead
    [[zP, zOne, zP], [zOne, zP, zOne]] 1 := by decide +kernel

private def wE1 : poly.PPoly := [[], poly.one]
private def wE2 : poly.PPoly := [poly.one, poly.one]

example : trigpencil.symbolAt [[wE1, wE2], [wE2, wE1]] 1 0 := by
  decide +kernel
example : ¬ trigpencil.symbolAt [[wE1, wE2], [wE2, wE1]] 2 0 := by
  decide +kernel

example : trigpencil.gradeBoundRead
    [[[BPair.ofNat 2, BPair.unit, BPair.unit]]] [0] := by decide +kernel
example : ¬ trigpencil.gradeBoundRead
    [[[BPair.unit, BPair.ofNat 2]]] [0] := by decide +kernel
