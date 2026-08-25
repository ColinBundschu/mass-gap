import MassGap.Wg
/-!
The check module for `prop:wg`: the batteries re-read the pairing
scheme by kernel `decide` at the fusion reads' instances.  The
Gram at one and two places (`d` and `det = d⁴ - d²`) with the
Weingarten solve's two class values (`1/(d²-1)` and
`-1/(d³-d)`); and the scheme's identity instances at the fusion
reads — `⟨tr U, tr U⟩ = 1`, `⟨1, 1⟩ = 1` at the presentation
`1 = [1 : d_f] tr(U U†)`, `⟨χ_adj, χ_adj⟩ = 1` with
`⟨1, χ_adj⟩` of equal members at
`χ_adj = |tr U|² - [1 : d_f] tr(U U†)`, `Eval(|tr U|⁴) = 2`,
`⟨(tr U)², tr U²⟩` of equal members, the conjugate pairing
`⟨tr(U U†), tr(U U†)⟩ = d²`, and the two-variable
`⟨tr(U V), tr(U V)⟩ = 1` — every value one polynomial pair in the
residue.  The member tier's batteries re-read `prop:wg`'s member
display at both engines: the `B`/`D` traces at the dimension
`r + 3` per loop and the `C` traces at the doubled rank `2r` with
the sign's flagship `Eval(tr U²) = -1`, the mixed two-variable
`Eval(tr(U V U† V†))` at `1 : (r+3)` and `1 : 2r`, and the
character orthonormality `⟨tr(U V), tr(U V)⟩ = 1` at both.  The
member tier's coverage closes at the dagger counts and the
wrappers: the unequal-dagger word at an even total,
`Eval((tr U)³ tr U†) = 3` on both engines, the odd-count read at
the sum's unit on a single factor, and one read through each
wrapper — `pairPhiSer` at `⟨tr U, tr U⟩ = 1` and `pairFullSer` at
the one-term pair's orthonormality, the hand-built data through
the fold. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground poly genericlift states wg

private def u : BPair := BPair.unit

/-! The Gram at one and two places, and the Weingarten solve's two
class values. -/

example : split.pmatOneValue (gramWg 1) [[[⟨2, 1⟩, ⟨2, 1⟩]]] := by
  decide +kernel
example : poly.oneValue (split.pminor (gramWg 2))
    [u, ⟨3, 1⟩, ⟨6, 1⟩, ⟨5, 1⟩, ⟨2, 1⟩] := by decide +kernel
example : crossNull (wgPair 2 [0, 1])
    ([⟨2, 1⟩], [u, ⟨3, 1⟩, ⟨2, 1⟩]) := by decide +kernel
example : crossNull (wgPair 2 [1, 0])
    ([⟨1, 2⟩], [u, ⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩]) := by decide +kernel
example : genericlift.adjRead (gramWg 2) := by decide +kernel

/-! The scheme's identity instances at the fusion reads. -/

private def fU : FList := [(false, false)]
private def fUU : FList := [(false, false), (false, false)]
private def fAdj : FList := [(false, false), (false, true)]
private def fUV : FList := [(false, false), (true, false)]

/-- The unit's presentation, `[1 : d_f] tr(U U†)`. -/
private def unitC : Comb := [([1, 0], ([⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]

/-- The adjoint character's presentation,
`|tr U|² - [1 : d_f] tr(U U†)`. -/
private def adjC : Comb :=
  [([0, 1], pOne), ([1, 0], ([⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]

example : crossNull (pairPhi fU fU [0] [0]) pOne := by decide +kernel
example : crossNull (pairFull fAdj fAdj unitC unitC) pOne := by decide +kernel
example : crossNull (pairFull fAdj fAdj adjC adjC) pOne := by decide +kernel
example : crossNull (pairFull fAdj fAdj unitC adjC) pZero := by decide +kernel
example : crossNull (pairPhi fUU fUU [0, 1] [0, 1])
    ([⟨3, 1⟩], [⟨2, 1⟩]) := by decide +kernel
example : crossNull (pairPhi fUU fUU [0, 1] [1, 0]) pZero := by decide +kernel
example : crossNull (pairPhi fAdj fAdj [1, 0] [1, 0])
    (poly.mul [⟨2, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩]) := by
  decide +kernel
example : crossNull (pairPhi fUV fUV [1, 0] [1, 0]) pOne := by decide +kernel

/-! The member tier: the `B`/`D` and `C` engines at the displayed
traces, every value validated against the member contraction. -/

/-- The dimension's polynomial, `r + 3`. -/
private def rP3 : Poly := [⟨4, 1⟩, ⟨2, 1⟩]

/-- The doubled rank's polynomial, `2r`. -/
private def r2 : Poly := [u, ⟨3, 1⟩]

private def fDD : FList := [(false, true), (false, true)]
private def fU4 : FList :=
  [(false, false), (false, false), (false, false), (false, false)]
private def fUUdd : FList :=
  [(false, false), (false, false), (false, true), (false, true)]
private def fUdUd : FList :=
  [(false, false), (false, true), (false, false), (false, true)]
private def fCyc : FList :=
  [(false, false), (true, false), (false, true), (true, true)]
private def fOrth : FList :=
  [(false, false), (true, false), (true, true), (false, true)]

/-! The `B`/`D` engine's single-variable traces. -/

example : crossNull (evalPhiBD fAdj [1, 0]) (rP3, poly.one) := by
  decide +kernel
example : crossNull (evalPhiBD fAdj [0, 1]) pOne := by decide +kernel
example : crossNull (evalPhiBD fUU [0, 1]) pOne := by decide +kernel
example : crossNull (evalPhiBD fUU [1, 0]) pOne := by decide +kernel
example : crossNull (evalPhiBD fDD [0, 1]) pOne := by decide +kernel
example : crossNull (evalPhiBD fU4 [0, 1, 2, 3])
    ([⟨4, 1⟩], poly.one) := by decide +kernel
example : crossNull (evalPhiBD fU4 [1, 2, 3, 0]) pOne := by decide +kernel
example : crossNull (evalPhiBD fU4 [1, 0, 3, 2])
    ([⟨4, 1⟩], poly.one) := by decide +kernel
example : crossNull (evalPhiBD fUUdd [1, 2, 3, 0])
    (rP3, poly.one) := by decide +kernel
example : crossNull (evalPhiBD fUdUd [1, 0, 3, 2])
    (poly.mul rP3 rP3, poly.one) := by decide +kernel
example : crossNull (evalPhiBD fUdUd [1, 2, 3, 0])
    (rP3, poly.one) := by decide +kernel
example : crossNull (evalPhiBD fUUdd [0, 1, 2, 3])
    ([⟨4, 1⟩], poly.one) := by decide +kernel
example : crossNull (evalPhiBD fUUdd [1, 0, 3, 2])
    ([⟨4, 1⟩], poly.one) := by decide +kernel

/-! The `C` engine's single-variable traces, the sign at the walk's
parity. -/

example : crossNull (evalPhiC fUU [0, 1]) pOne := by decide +kernel
example : crossNull (evalPhiC fUU [1, 0])
    (poly.neg poly.one, poly.one) := by decide +kernel
example : crossNull (evalPhiC fAdj [1, 0]) (r2, poly.one) := by
  decide +kernel
example : crossNull (evalPhiC fAdj [0, 1]) pOne := by decide +kernel
example : crossNull (evalPhiC fDD [1, 0])
    (poly.neg poly.one, poly.one) := by decide +kernel
example : crossNull (evalPhiC fU4 [0, 1, 2, 3])
    ([⟨4, 1⟩], poly.one) := by decide +kernel
example : crossNull (evalPhiC fU4 [1, 2, 3, 0])
    (poly.neg poly.one, poly.one) := by decide +kernel
example : crossNull (evalPhiC fU4 [1, 0, 3, 2])
    ([⟨4, 1⟩], poly.one) := by decide +kernel
example : crossNull (evalPhiC fUUdd [1, 2, 3, 0])
    (r2, poly.one) := by decide +kernel
example : crossNull (evalPhiC fUdUd [1, 0, 3, 2])
    (poly.mul r2 r2, poly.one) := by decide +kernel
example : crossNull (evalPhiC fUdUd [1, 2, 3, 0])
    (r2, poly.one) := by decide +kernel
example : crossNull (evalPhiC fUUdd [0, 1, 2, 3])
    ([⟨4, 1⟩], poly.one) := by decide +kernel
example : crossNull (evalPhiC fUUdd [1, 0, 3, 2])
    ([⟨4, 1⟩], poly.one) := by decide +kernel

/-! The mixed two-variable pins: the inner Schur average at the
dimension's cofactor, and the character orthonormality. -/

example : crossNull (evalPhiBD fCyc [1, 2, 3, 0])
    (poly.one, rP3) := by decide +kernel
example : crossNull (evalPhiC fCyc [1, 2, 3, 0])
    (poly.one, r2) := by decide +kernel
example : crossNull (evalPhiBD fOrth [1, 0, 3, 2]) pOne := by decide +kernel
example : crossNull (evalPhiC fOrth [1, 0, 3, 2]) pOne := by decide +kernel

/-! The dagger-count coverage: the unequal-dagger word at an even
total, `(tr U)³ tr U†` at the identity wiring reading `3` on both
engines, and the odd-count read at the sum's unit on a single
factor. -/

private def fCube : FList :=
  [(false, false), (false, false), (false, false), (false, true)]

example : crossNull (evalPhiBD fCube [0, 1, 2, 3])
    ([⟨4, 1⟩], poly.one) := by decide +kernel
example : crossNull (evalPhiC fCube [0, 1, 2, 3])
    ([⟨4, 1⟩], poly.one) := by decide +kernel
example : crossNull (evalPhiBD fU [0]) pZero := by decide +kernel
example : crossNull (evalPhiC fU [0]) pZero := by decide +kernel

/-! One read through each wrapper: `pairPhiSer` at
`⟨tr U, tr U⟩ = 1`, and `pairFullSer` at the one-term pair's
orthonormality — the hand-built `fOrth` data through the bilinear
fold. -/

example : crossNull (pairPhiSer evalPhiBD fU fU [0] [0]) pOne := by
  decide +kernel
example : crossNull (pairFullSer evalPhiBD fUV fUV
    [([1, 0], pOne)] [([1, 0], pOne)]) pOne := by decide +kernel
