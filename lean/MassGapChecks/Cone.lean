import MassGap.Cone
/-!
The check module for `lem:cone`: the batteries read the cone read by
kernel `decide` at two directions beside the theorem routes.

The profile block reads a committed momentum profile: the unit
monomial's symbol `x² − 5x + 6` at the vacant grid, the isotropic
coefficient `3` at both squares, the quartic coefficient `2x − 1` at
both fourth powers and the cross coefficient `4` at the paired
squares, every further grid the vacant polynomial.  The profile is
decided invariant at every degree through four, and two forged
profiles isolate the read's two clauses — a profile occupied at a
grid of odd coordinate total refuses the reflection at degree one
while surviving degree two, and a profile vacant at one square
alone refuses the transposition at degree two while surviving
degree one.  The three degree reads are routed at the profile and
decided beside their routes: the isotropic square at the second
square's grid and at the cross grid (the scale by the square's
indicator reading the vacant polynomial there), the odd vacancy at
a degree-three grid, and the degree-four read at the cross grid and
at a fourth power; the membership binder is isolated at a grid of
degree three decided off the degree-two box, where a profile
occupied there is still decided invariant at degree two while the
isotropic identity refuses, at a grid of degree six off the
degree-four box for the direction read, and at the square's grid
off the degree-three box for the odd vacancy, whose parity binder
the degree-two instance isolates beside it, the profile invariant
there and the square's coefficient off the unit.  The cone read consumes the profile at one
component.

The root block reads the located coefficient at the extension
`x² − 2` bracketed at `[5 : 4]` and `[3 : 2]`, the isolation at the
width `[1 : 4]`, the symbol `(x² − 2)(x − 3)` at its root and the
derivative's witness `(4 + 6x)(3x² − 6x − 2) + (24 − 18x)(x² − 2)
= −56`: the root read decided, its root conjunct isolated at the
extension `x² − 3` (the bracket, the isolation and a witness
holding there while the symbol reads off the unit at its root),
the witness conjunct at a forged cofactor; the coefficient's
cofactor reads `−12 − 18x` and its identity `ā S₀' − 56 · 3` at the
extension's multiple is routed through `locCoef_read` and decided,
with the identity refused at a forged cofactor and the witness
binder isolated at a forged witness whose cofactor reads the
identity off the unit; the coefficient at the profile is routed
through `prof_coef`, the profile's unit-monomial polynomial the
symbol and its square polynomial the isotropic coefficient.

The locus block reads the decimated determinant's root locus at a
symmetric two-by-two pencil, `1 + x` and `4 + x` on the diagonal
with the coupling `2`, at the clearing power one and the pivot at
the first key: at the level one both determinants sit off the
unit and at the level nought both read it, each direction routed
through `locus_defl` beside the decided pair; the pivot binder is
isolated at the level minus one, where the pivot reads the unit
and the two determinants part; the shape binder at a pencil
holding a square coupling beyond the clearing power, read at the
point one over the clearing two, where the saturated evaluation
parts from the deflation's; and the permutation binder at the
repeated key, the two determinants parting at the level one — the
symmetry binder `thm:pairpencil`'s frame recorded at an asymmetric
pencil whose two determinants still read together, and the pivot
orders `lem:cellcount`'s designated places' frame.
-/

open ground poly cone

/-! The committed momentum profile at two directions. -/

private def cS0 : Poly := [⟨7, 1⟩, ⟨1, 3⟩, ⟨1, 4⟩, ⟨2, 1⟩]
private def cS2 : Poly := [⟨4, 1⟩]
private def cQ : Poly := [⟨1, 2⟩, ⟨3, 1⟩]
private def cC : Poly := [⟨5, 1⟩]

private def cF (g : List (List Nat)) : Poly :=
  if g == [[0, 0]] then cS0
  else if g == [[2, 0]] || g == [[0, 2]] then cS2
  else if g == [[4, 0]] || g == [[0, 4]] then cQ
  else if g == [[2, 2]] then cC
  else []

example : vacG 2 = [[0, 0]] := by decide +kernel
example : isoG 2 = [[2, 0]] := by decide +kernel
example : 0 < ground.countOf (vacG 2) (restoration.momBox 1 2 0) := by
  decide +kernel
example : 0 < ground.countOf (isoG 2) (restoration.momBox 1 2 2) := by
  decide +kernel

example : profRead 2 cF := by decide +kernel
example : bdInvP 2 1 cF := by decide +kernel
example : bdInvP 2 2 cF := by decide +kernel
example : bdInvP 2 3 cF := by decide +kernel
example : bdInvP 2 4 cF := by decide +kernel

/-! The two clauses isolated: an odd occupancy refuses the
reflection alone, a one-sided vacancy the transposition alone. -/

private def oddForge (g : List (List Nat)) : Poly :=
  if g == [[1, 0]] then [⟨2, 1⟩] else cF g

example : ¬ bdInvP 2 1 oddForge := by decide +kernel
example : bdInvP 2 2 oddForge := by decide +kernel

private def swapForge (g : List (List Nat)) : Poly :=
  if g == [[0, 2]] then [] else cF g

example : ¬ bdInvP 2 2 swapForge := by decide +kernel
example : bdInvP 2 1 swapForge := by decide +kernel

/-! The degree-two read at the second square and at the cross grid,
routed and decided. -/

example : oneValue (cF [[0, 2]])
    (scaleP (restoration.ipFam 1 2 0 0 [[0, 2]]) (cF (isoG 2))) :=
  deg2_iso 2 cF (by decide +kernel) [[0, 2]] (by decide +kernel)
example : oneValue (cF [[0, 2]])
    (scaleP (restoration.ipFam 1 2 0 0 [[0, 2]]) (cF (isoG 2))) := by
  decide +kernel
example : oneValue (cF [[1, 1]])
    (scaleP (restoration.ipFam 1 2 0 0 [[1, 1]]) (cF (isoG 2))) :=
  deg2_iso 2 cF (by decide +kernel) [[1, 1]] (by decide +kernel)
example : oneValue (cF [[1, 1]])
    (scaleP (restoration.ipFam 1 2 0 0 [[1, 1]]) (cF (isoG 2))) := by
  decide +kernel

/-! The membership binder isolated at a grid of degree three off the
box: the forged profile is invariant at degree two while the
isotropic identity refuses there. -/

private def offBox (g : List (List Nat)) : Poly :=
  if g == [[3, 0]] then [⟨2, 1⟩] else cF g

example : ground.countOf [[3, 0]] (restoration.momBox 1 2 2) = 0 := by
  decide +kernel
example : bdInvP 2 2 offBox := by decide +kernel
example : ¬ oneValue (offBox [[3, 0]])
    (scaleP (restoration.ipFam 1 2 0 0 [[3, 0]]) (offBox (isoG 2))) := by
  decide +kernel

/-! The odd vacancy at degree three; the membership binder isolated
at the square's grid off the degree-three box and the parity binder
at degree two, the one cell refusing both. -/

example : unitTail (cF [[2, 1]]) :=
  odd_vac 2 3 rfl cF (by decide +kernel) [[2, 1]] (by decide +kernel)
example : unitTail (cF [[2, 1]]) := by decide +kernel
example : ground.countOf [[2, 0]] (restoration.momBox 1 2 3) = 0 := by
  decide +kernel
example : bdInvP 2 3 cF := by decide +kernel
example : ¬ unitTail (cF [[2, 0]]) := by decide +kernel

/-! The degree-four read at the cross grid and at a fourth power,
routed and decided. -/

example : oneValue (add (cF [[2, 2]]) (cF [[2, 2]]))
    (add (scaleP (restoration.prodIP 1 2 0 0 0 0 [[2, 2]])
        (cF (restoration.crossG 2 0 1)))
      (scaleP (restoration.quFam 1 2 0 [[2, 2]])
        (add (add (cF (restoration.quGrid 1 2 0 0))
            (cF (restoration.quGrid 1 2 0 0)))
          (neg (cF (restoration.crossG 2 0 1)))))) :=
  deg4_dir 2 cF (by decide +kernel) [[2, 2]] (by decide +kernel)
example : oneValue (add (cF [[2, 2]]) (cF [[2, 2]]))
    (add (scaleP (restoration.prodIP 1 2 0 0 0 0 [[2, 2]])
        (cF (restoration.crossG 2 0 1)))
      (scaleP (restoration.quFam 1 2 0 [[2, 2]])
        (add (add (cF (restoration.quGrid 1 2 0 0))
            (cF (restoration.quGrid 1 2 0 0)))
          (neg (cF (restoration.crossG 2 0 1)))))) := by
  decide +kernel
example : oneValue (add (cF [[0, 4]]) (cF [[0, 4]]))
    (add (scaleP (restoration.prodIP 1 2 0 0 0 0 [[0, 4]])
        (cF (restoration.crossG 2 0 1)))
      (scaleP (restoration.quFam 1 2 0 [[0, 4]])
        (add (add (cF (restoration.quGrid 1 2 0 0))
            (cF (restoration.quGrid 1 2 0 0)))
          (neg (cF (restoration.crossG 2 0 1)))))) :=
  deg4_dir 2 cF (by decide +kernel) [[0, 4]] (by decide +kernel)
example : oneValue (add (cF [[0, 4]]) (cF [[0, 4]]))
    (add (scaleP (restoration.prodIP 1 2 0 0 0 0 [[0, 4]])
        (cF (restoration.crossG 2 0 1)))
      (scaleP (restoration.quFam 1 2 0 [[0, 4]])
        (add (add (cF (restoration.quGrid 1 2 0 0))
            (cF (restoration.quGrid 1 2 0 0)))
          (neg (cF (restoration.crossG 2 0 1)))))) := by
  decide +kernel

/-! The direction read's membership binder isolated at a grid of
degree six off the box: the forged profile is invariant at degree
four while the direction identity refuses there. -/

private def offSix (g : List (List Nat)) : Poly :=
  if g == [[6, 0]] then [⟨2, 1⟩] else cF g

example : ground.countOf [[6, 0]] (restoration.momBox 1 2 4) = 0 := by
  decide +kernel
example : bdInvP 2 4 offSix := by decide +kernel
example : ¬ oneValue (add (offSix [[6, 0]]) (offSix [[6, 0]]))
    (add (scaleP (restoration.prodIP 1 2 0 0 0 0 [[6, 0]])
        (offSix (restoration.crossG 2 0 1)))
      (scaleP (restoration.quFam 1 2 0 [[6, 0]])
        (add (add (offSix (restoration.quGrid 1 2 0 0))
            (offSix (restoration.quGrid 1 2 0 0)))
          (neg (offSix (restoration.crossG 2 0 1)))))) := by
  decide +kernel

/-! The cone read at the profile, its isotropic component read at
the first square. -/

example : oneValue (cF [[2, 0]])
    (scaleP (restoration.ipFam 1 2 0 0 [[2, 0]]) (cF (isoG 2))) :=
  (cone_read 2 cF (by decide +kernel)).1 [[2, 0]] (by decide +kernel)

/-! The located coefficient at the extension `x² − 2`. -/

private def cE : stage.Ext :=
  ⟨[⟨1, 3⟩, BPair.unit], ⟨⟨6, 1⟩, 4⟩, ⟨⟨4, 1⟩, 2⟩⟩
private def cU : Poly := [⟨5, 1⟩, ⟨7, 1⟩]
private def cV : Poly := [⟨25, 1⟩, ⟨1, 19⟩]
private def c1 : BPair := ⟨1, 57⟩

example : stage.bracketRead cE := by decide +kernel
example : stage.isolRead cE 1 4 := by decide +kernel
example : stage.reduceRead cE cS0 := by decide +kernel
example : stage.witnessRead cE (deriv cS0) cU cV c1 := by decide +kernel
example : rootRead cE cS0 cU cV c1 1 4 := by decide +kernel

/-! The root conjunct isolated at the extension `x² − 3`, the
bracket, the isolation and a witness holding there; the witness
conjunct at a forged cofactor. -/

private def cE3 : stage.Ext :=
  ⟨[⟨1, 4⟩, BPair.unit], ⟨⟨13, 1⟩, 8⟩, ⟨⟨15, 1⟩, 8⟩⟩
private def cU3 : Poly := [⟨8, 1⟩, ⟨7, 1⟩]
private def cV3 : Poly := [⟨16, 1⟩, ⟨1, 19⟩]

example : stage.bracketRead cE3 := by decide +kernel
example : stage.isolRead cE3 1 4 := by decide +kernel
example : stage.witnessRead cE3 (deriv cS0) cU3 cV3 ⟨1, 60⟩ := by
  decide +kernel
example : ¬ stage.reduceRead cE3 cS0 := by decide +kernel
example : ¬ rootRead cE3 cS0 cU3 cV3 ⟨1, 60⟩ 1 4 := by decide +kernel

example : ¬ stage.witnessRead cE (deriv cS0) cU [⟨25, 1⟩] c1 := by
  decide +kernel
example : ¬ rootRead cE cS0 cU [⟨25, 1⟩] c1 1 4 := by decide +kernel

/-! The cofactor's value and its identity, routed and decided; the
identity refused at a forged cofactor, the witness binder isolated
at a forged witness, and the coefficient at the profile routed
through `prof_coef` at the profile whose unit-monomial polynomial
is the symbol. -/

example : oneValue (locCoef cE cS2 cU) [⟨1, 13⟩, ⟨1, 19⟩] := by
  decide +kernel

example : stage.reduceRead cE
    (add (mul (locCoef cE cS2 cU) (deriv cS0)) (scaleP c1 cS2)) :=
  locCoef_read cE cS0 cS2 cU cV c1 (by decide +kernel)
example : stage.reduceRead cE
    (add (mul (locCoef cE cS2 cU) (deriv cS0)) (scaleP c1 cS2)) := by
  decide +kernel
example : ¬ stage.reduceRead cE
    (add (mul [⟨1, 13⟩] (deriv cS0)) (scaleP c1 cS2)) := by decide +kernel

private def uForge : Poly := [⟨5, 1⟩]

private def cG (g : List (List Nat)) : Poly :=
  if g == [[0, 0]] then cS0 else cF g

example : rootRead cE (cG (vacG 2)) cU cV c1 1 4 := by decide +kernel
example : stage.reduceRead cE
    (add (mul (locCoef cE (cG (isoG 2)) cU) (deriv (cG (vacG 2))))
      (scaleP c1 (cG (isoG 2)))) :=
  prof_coef 2 cG cE cU cV c1 1 4 (by decide +kernel)
example : stage.reduceRead cE
    (add (mul (locCoef cE (cG (isoG 2)) cU) (deriv (cG (vacG 2))))
      (scaleP c1 (cG (isoG 2)))) := by decide +kernel

example : ¬ stage.witnessRead cE (deriv cS0) uForge cV c1 := by
  decide +kernel
example : ¬ stage.reduceRead cE
    (add (mul (locCoef cE cS2 uForge) (deriv cS0)) (scaleP c1 cS2)) := by
  decide +kernel

/-! The decimated determinant's root locus at the committed pencil. -/

private def lP : split.PMat :=
  [[[⟨2, 1⟩, ⟨2, 1⟩], [⟨3, 1⟩]], [[⟨3, 1⟩], [⟨5, 1⟩, ⟨2, 1⟩]]]

example : cellcount.pShapeAt lP 2 1 := by decide +kernel
example : split.pSymAt lP 2 := by decide +kernel
example : 0 < ground.countOf ([0] ++ [1]) (places.perms 2) := by
  decide +kernel

/-! At the level one both determinants sit off the unit, at the level
nought both read it. -/

example : ¬ (elim.minor (elim.selM [0] [0] (cellcount.evalPC lP ⟨2, 1⟩ 1 1))).oneValue BPair.unit := by decide +kernel
example : ¬ (elim.minor (cellcount.evalPC (cellcount.pdefl [0] [1] lP)
    ⟨2, 1⟩ 1 ((2 * ([0] : List Nat).length + 1) * 1))).oneValue
      BPair.unit := by decide +kernel
example : ¬ (elim.minor (cellcount.evalPC lP ⟨2, 1⟩ 1 1)).oneValue
    BPair.unit := by decide +kernel
example : ¬ (elim.minor (cellcount.evalPC (cellcount.pdefl [0] [1] lP)
    ⟨2, 1⟩ 1 ((2 * ([0] : List Nat).length + 1) * 1))).oneValue
      BPair.unit :=
  fun h => (by decide +kernel : ¬ (elim.minor
      (cellcount.evalPC lP ⟨2, 1⟩ 1 1)).oneValue BPair.unit)
    ((locus_defl (o := 2) lP 1 [0] [1] ⟨2, 1⟩ 1 (by decide +kernel)
      (by decide +kernel) (Or.inl rfl) (by decide +kernel)
      (by decide +kernel)).mp h)

example : ¬ (elim.minor (elim.selM [0] [0] (cellcount.evalPC lP ⟨1, 1⟩ 1 1))).oneValue BPair.unit := by decide +kernel
example : (elim.minor (cellcount.evalPC (cellcount.pdefl [0] [1] lP)
    ⟨1, 1⟩ 1 ((2 * ([0] : List Nat).length + 1) * 1))).oneValue
      BPair.unit := by decide +kernel
example : (elim.minor (cellcount.evalPC lP ⟨1, 1⟩ 1 1)).oneValue
    BPair.unit := by decide +kernel
example : (elim.minor (cellcount.evalPC (cellcount.pdefl [0] [1] lP)
    ⟨1, 1⟩ 1 ((2 * ([0] : List Nat).length + 1) * 1))).oneValue
      BPair.unit :=
  (locus_defl (o := 2) lP 1 [0] [1] ⟨1, 1⟩ 1 (by decide +kernel)
    (by decide +kernel) (Or.inl rfl) (by decide +kernel)
    (by decide +kernel)).mpr
    (by decide +kernel)

/-! The pivot binder isolated at the level minus one, where the
pivot reads the unit and the two determinants part. -/

example : (elim.minor (elim.selM [0] [0] (cellcount.evalPC lP ⟨1, 2⟩ 1 1))).oneValue BPair.unit := by decide +kernel
example : ¬ ((elim.minor (cellcount.evalPC (cellcount.pdefl [0] [1] lP)
      ⟨1, 2⟩ 1 ((2 * ([0] : List Nat).length + 1) * 1))).oneValue
        BPair.unit
    ↔ (elim.minor (cellcount.evalPC lP ⟨1, 2⟩ 1 1)).oneValue
        BPair.unit) := by decide +kernel

/-! The symmetry binder is `thm:pairpencil`'s frame, the route's
own datum at the transposed coupling: at the couplings `2` against
`3` the pencil refuses the symmetry while the two determinants read
together at the level nought, the deflation's cleared display
reading the lower coupling itself. -/

private def lA : split.PMat :=
  [[[⟨2, 1⟩, ⟨2, 1⟩], [⟨3, 1⟩]], [[⟨4, 1⟩], [⟨5, 1⟩, ⟨2, 1⟩]]]

example : cellcount.pShapeAt lA 2 1 := by decide +kernel
example : ¬ split.pSymAt lA 2 := by decide +kernel
example : ((elim.minor (cellcount.evalPC (cellcount.pdefl [0] [1] lA)
      ⟨1, 1⟩ 1 ((2 * ([0] : List Nat).length + 1) * 1))).oneValue
        BPair.unit
    ↔ (elim.minor (cellcount.evalPC lA ⟨1, 1⟩ 1 1)).oneValue
        BPair.unit) := by decide +kernel

/-! The shape binder isolated at a square term beyond the clearing
power: the truncated evaluation reads the unit while the deflation's
sits off it. -/

private def lB : split.PMat :=
  [[[⟨2, 1⟩, ⟨2, 1⟩], [BPair.unit, BPair.unit, ⟨2, 1⟩]],
   [[BPair.unit, BPair.unit, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]]]

example : ¬ cellcount.pShapeAt lB 2 1 := by decide +kernel
example : split.pSymAt lB 2 := by decide +kernel
example : ¬ (elim.minor (elim.selM [0] [0] (cellcount.evalPC lB ⟨3, 1⟩ 2 1))).oneValue BPair.unit := by decide +kernel
example : ¬ ((elim.minor (cellcount.evalPC (cellcount.pdefl [0] [1] lB)
      ⟨3, 1⟩ 2 ((2 * ([0] : List Nat).length + 1) * 1))).oneValue
        BPair.unit
    ↔ (elim.minor (cellcount.evalPC lB ⟨3, 1⟩ 2 1)).oneValue
        BPair.unit) := by decide +kernel

/-! The permutation binder isolated at the repeated key, the two
determinants parting at the level one. -/

example : ¬ (0 < ground.countOf ([0] ++ [0]) (places.perms 2)) := by
  decide +kernel
example : ¬ ((elim.minor (cellcount.evalPC (cellcount.pdefl [0] [0] lP)
      ⟨2, 1⟩ 1 ((2 * ([0] : List Nat).length + 1) * 1))).oneValue
        BPair.unit
    ↔ (elim.minor (cellcount.evalPC lP ⟨2, 1⟩ 1 1)).oneValue
        BPair.unit) := by decide +kernel
