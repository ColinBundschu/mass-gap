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
wrapper — `pairPhi` at `⟨tr U, tr U⟩ = 1` and `pairFull` at the
one-term pair's orthonormality, the hand-built data through the
fold.  The evaluator over the site's own variables reads beside
the two-plaquette instances: the variable list's pins, a site at
the keys `0` and `2` and one at `5` and `2` reading one value with
the keys `0` and `1`, the three-variable trace product at `d_f³`,
the three-character orthonormality, the mismatched dagger count's
refusal, and the member engines at a key-`2` adjoint site.  The
transport tier closes the module: the Gram
determinant's occupancy at the first three counts, and the Gram's
transport symmetry with the Weingarten column's travel at the
two-place cell — abelian, so the relabeling acts trivially and the
cell is a clearance — and at two three-place cells, the second
moving the key's place from two to one, each decided beside its
theorem route, with the relabeling's membership binder refused at
a repeated word.  The gauge-mode tier closes the module: the
evaluation at a relabeled site and its carried wiring against the
site's own — the same-site cell at the exchanged undaggered
places, the cross-site cell at the swapped blocks, and the
two-variable cell at the exchanged daggered places, each with the
site's and the wiring's motion decided beside it and landed by the
theorem route — with both membership binders refused at exhibited
words and a forged wiring reading the cross null anyway. -/

namespace wg
set_option maxHeartbeats 4000000

open ground poly genericlift states

private def u : BPair := BPair.unit

/-! The Gram at one and two places, and the Weingarten solve's two
class values. -/

theorem pin1 : split.pmatOneValue (gramWg 1) [[[⟨2, 1⟩, ⟨2, 1⟩]]] := by
  decide +kernel
theorem pin2 : poly.oneValue (split.pminor (gramWg 2))
    [u, ⟨3, 1⟩, ⟨6, 1⟩, ⟨5, 1⟩, ⟨2, 1⟩] := by decide +kernel
theorem pin3 : crossNull (wgPair 2 [0, 1])
    ([⟨2, 1⟩], [u, ⟨3, 1⟩, ⟨2, 1⟩]) := by decide +kernel
theorem pin4 : crossNull (wgPair 2 [1, 0])
    ([⟨1, 2⟩], [u, ⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩]) := by decide +kernel
theorem pin5 : split.adjRead (gramWg 2) := by decide +kernel

/-! The scheme's identity instances at the fusion reads. -/

private def fU : FList := [(0, false)]
private def fUU : FList := [(0, false), (0, false)]
private def fAdj : FList := [(0, false), (0, true)]
private def fUV : FList := [(0, false), (1, false)]

/-- The unit's presentation, `[1 : d_f] tr(U U†)`. -/
private def unitC : Comb := [([1, 0], ([⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]

/-- The adjoint character's presentation,
`|tr U|² - [1 : d_f] tr(U U†)`. -/
private def adjC : Comb :=
  [([0, 1], pOne), ([1, 0], ([⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]

theorem pin6 : crossNull (pairPhi evalPhi fU fU [0] [0]) pOne := by decide +kernel
theorem pin7 : crossNull (pairFull evalPhi fAdj fAdj unitC unitC) pOne := by decide +kernel
theorem pin8 : crossNull (pairFull evalPhi fAdj fAdj adjC adjC) pOne := by decide +kernel
theorem pin9 : crossNull (pairFull evalPhi fAdj fAdj unitC adjC) pZero := by decide +kernel
theorem pin10 : crossNull (pairPhi evalPhi fUU fUU [0, 1] [0, 1])
    ([⟨3, 1⟩], [⟨2, 1⟩]) := by decide +kernel
theorem pin11 : crossNull (pairPhi evalPhi fUU fUU [0, 1] [1, 0]) pZero := by decide +kernel
theorem pin12 : crossNull (pairPhi evalPhi fAdj fAdj [1, 0] [1, 0])
    (poly.mul [⟨2, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩]) := by
  decide +kernel
theorem pin13 : crossNull (pairPhi evalPhi fUV fUV [1, 0] [1, 0]) pOne := by decide +kernel

/-! The member tier: the `B`/`D` and `C` engines at the displayed
traces, every value validated against the member contraction. -/

/-- The dimension's polynomial, `r + 3`. -/
private def rP3 : Poly := [⟨4, 1⟩, ⟨2, 1⟩]

/-- The doubled rank's polynomial, `2r`. -/
private def r2 : Poly := [u, ⟨3, 1⟩]

private def fDD : FList := [(0, true), (0, true)]
private def fU4 : FList :=
  [(0, false), (0, false), (0, false), (0, false)]
private def fUUdd : FList :=
  [(0, false), (0, false), (0, true), (0, true)]
private def fUdUd : FList :=
  [(0, false), (0, true), (0, false), (0, true)]
private def fCyc : FList :=
  [(0, false), (1, false), (0, true), (1, true)]
private def fOrth : FList :=
  [(0, false), (1, false), (1, true), (0, true)]

/-! The evaluator over the site's own variables: the variable list
at the occupied keys in their order (`varsOf`), the two-plaquette
reads above its instances at the keys `0` and `1`; a site at the
keys `0` and `2`, and one at `5` and `2`, reads one value with its
relabeling at the keys `0` and `1`, the keys' names, gaps and order
off the value; the three-variable site `tr(U U†) tr(V V†) tr(W W†)`
reads `d_f³`; the product of three fundamental characters on three
variables is orthonormal, `⟨tr U tr V tr W, tr U tr V tr W⟩ = 1`;
and a mismatched dagger count at a variable reads the sum's unit,
the matched two-variable site occupied. -/

private def f3 : FList := [(0, false), (1, false), (2, false)]
private def f33 : FList :=
  [(0, false), (1, false), (2, false), (0, true), (1, true), (2, true)]
private def f02 : FList := [(0, false), (2, false), (0, true), (2, true)]
private def f52 : FList := [(5, false), (2, false), (5, true), (2, true)]
private def dfP : Poly := [⟨2, 1⟩, ⟨2, 1⟩]

theorem pin14 : varsOf fCyc = [0, 1] := by decide +kernel
theorem pin15 : varsOf f02 = [0, 2] := by decide +kernel
theorem pin16 : varsOf f52 = [2, 5] := by decide +kernel
theorem pin17 : varsOf ([] : FList) = [] := by decide +kernel
theorem pin18 : crossNull (evalPhi f02 [2, 3, 0, 1]) (evalPhi fCyc [2, 3, 0, 1]) := by
  decide +kernel
theorem pin19 : crossNull (evalPhi f52 [1, 2, 3, 0]) (evalPhi fCyc [1, 2, 3, 0]) := by
  decide +kernel
theorem pin20 : crossNull (evalPhi f02 [2, 3, 0, 1]) (poly.mul dfP dfP, poly.one) := by
  decide +kernel
theorem pin21 : crossNull (evalPhi f33 [3, 4, 5, 0, 1, 2])
    (poly.mul dfP (poly.mul dfP dfP), poly.one) := by decide +kernel
theorem pin22 : crossNull (pairPhi evalPhi f3 f3 [0, 1, 2] [0, 1, 2]) pOne := by
  decide +kernel
theorem pin23 : crossNull (evalPhi fUV [1, 0]) pZero := by decide +kernel
theorem pin24 : ¬ crossNull (evalPhi fCyc [2, 3, 0, 1]) pZero := by decide +kernel

/-! The `B`/`D` engine's single-variable traces. -/

theorem pin25 : crossNull (evalPhiBD fAdj [1, 0]) (rP3, poly.one) := by
  decide +kernel
theorem pin26 : crossNull (evalPhiBD fAdj [0, 1]) pOne := by decide +kernel
theorem pin27 : crossNull (evalPhiBD fUU [0, 1]) pOne := by decide +kernel
theorem pin28 : crossNull (evalPhiBD fUU [1, 0]) pOne := by decide +kernel
theorem pin29 : crossNull (evalPhiBD fDD [0, 1]) pOne := by decide +kernel
theorem pin30 : crossNull (evalPhiBD fU4 [0, 1, 2, 3])
    ([⟨4, 1⟩], poly.one) := by decide +kernel
theorem pin31 : crossNull (evalPhiBD fU4 [1, 2, 3, 0]) pOne := by decide +kernel
theorem pin32 : crossNull (evalPhiBD fU4 [1, 0, 3, 2])
    ([⟨4, 1⟩], poly.one) := by decide +kernel
theorem pin33 : crossNull (evalPhiBD fUUdd [1, 2, 3, 0])
    (rP3, poly.one) := by decide +kernel
theorem pin34 : crossNull (evalPhiBD fUdUd [1, 0, 3, 2])
    (poly.mul rP3 rP3, poly.one) := by decide +kernel
theorem pin35 : crossNull (evalPhiBD fUdUd [1, 2, 3, 0])
    (rP3, poly.one) := by decide +kernel
theorem pin36 : crossNull (evalPhiBD fUUdd [0, 1, 2, 3])
    ([⟨4, 1⟩], poly.one) := by decide +kernel
theorem pin37 : crossNull (evalPhiBD fUUdd [1, 0, 3, 2])
    ([⟨4, 1⟩], poly.one) := by decide +kernel

/-! The `C` engine's single-variable traces, the sign at the walk's
parity. -/

theorem pin38 : crossNull (evalPhiC fUU [0, 1]) pOne := by decide +kernel
theorem pin39 : crossNull (evalPhiC fUU [1, 0])
    (poly.neg poly.one, poly.one) := by decide +kernel
theorem pin40 : crossNull (evalPhiC fAdj [1, 0]) (r2, poly.one) := by
  decide +kernel
theorem pin41 : crossNull (evalPhiC fAdj [0, 1]) pOne := by decide +kernel

/-! The member engines at a key-`2` adjoint site read the key-`0`
values. -/

private def fAdj2 : FList := [(2, false), (2, true)]

theorem pin42 : crossNull (evalPhiBD fAdj2 [1, 0]) (rP3, poly.one) := by
  decide +kernel
theorem pin43 : crossNull (evalPhiBD fAdj2 [0, 1]) pOne := by decide +kernel
theorem pin44 : crossNull (evalPhiC fAdj2 [1, 0]) (r2, poly.one) := by
  decide +kernel
theorem pin45 : crossNull (evalPhiC fAdj2 [0, 1]) pOne := by decide +kernel
theorem pin46 : crossNull (evalPhiC fDD [1, 0])
    (poly.neg poly.one, poly.one) := by decide +kernel
theorem pin47 : crossNull (evalPhiC fU4 [0, 1, 2, 3])
    ([⟨4, 1⟩], poly.one) := by decide +kernel
theorem pin48 : crossNull (evalPhiC fU4 [1, 2, 3, 0])
    (poly.neg poly.one, poly.one) := by decide +kernel
theorem pin49 : crossNull (evalPhiC fU4 [1, 0, 3, 2])
    ([⟨4, 1⟩], poly.one) := by decide +kernel
theorem pin50 : crossNull (evalPhiC fUUdd [1, 2, 3, 0])
    (r2, poly.one) := by decide +kernel
theorem pin51 : crossNull (evalPhiC fUdUd [1, 0, 3, 2])
    (poly.mul r2 r2, poly.one) := by decide +kernel
theorem pin52 : crossNull (evalPhiC fUdUd [1, 2, 3, 0])
    (r2, poly.one) := by decide +kernel
theorem pin53 : crossNull (evalPhiC fUUdd [0, 1, 2, 3])
    ([⟨4, 1⟩], poly.one) := by decide +kernel
theorem pin54 : crossNull (evalPhiC fUUdd [1, 0, 3, 2])
    ([⟨4, 1⟩], poly.one) := by decide +kernel

/-! The mixed two-variable pins: the inner Schur average at the
dimension's cofactor, and the character orthonormality. -/

theorem pin55 : crossNull (evalPhiBD fCyc [1, 2, 3, 0])
    (poly.one, rP3) := by decide +kernel
theorem pin56 : crossNull (evalPhiC fCyc [1, 2, 3, 0])
    (poly.one, r2) := by decide +kernel
theorem pin57 : crossNull (evalPhiBD fOrth [1, 0, 3, 2]) pOne := by decide +kernel
theorem pin58 : crossNull (evalPhiC fOrth [1, 0, 3, 2]) pOne := by decide +kernel

/-! The dagger-count coverage: the unequal-dagger word at an even
total, `(tr U)³ tr U†` at the identity wiring reading `3` on both
engines, and the odd-count read at the sum's unit on a single
factor. -/

private def fCube : FList :=
  [(0, false), (0, false), (0, false), (0, true)]

theorem pin59 : crossNull (evalPhiBD fCube [0, 1, 2, 3])
    ([⟨4, 1⟩], poly.one) := by decide +kernel
theorem pin60 : crossNull (evalPhiC fCube [0, 1, 2, 3])
    ([⟨4, 1⟩], poly.one) := by decide +kernel
theorem pin61 : crossNull (evalPhiBD fU [0]) pZero := by decide +kernel
theorem pin62 : crossNull (evalPhiC fU [0]) pZero := by decide +kernel

/-! One read through each wrapper: `pairPhi evalPhi` at
`⟨tr U, tr U⟩ = 1`, and `pairFull evalPhi` at the one-term pair's
orthonormality — the hand-built `fOrth` data through the bilinear
fold. -/

theorem pin63 : crossNull (pairPhi evalPhiBD fU fU [0] [0]) pOne := by
  decide +kernel
theorem pin64 : crossNull (pairFull evalPhiBD fUV fUV
    [([1, 0], pOne)] [([1, 0], pOne)]) pOne := by decide +kernel

/-! The transport tier at `con:sertables`' place carrier: the Gram
determinant's occupancy at the first three counts, the Gram's
transport symmetry and the Weingarten column's travel at the two-
and three-place cells, each decided beside its theorem route.  The
two-place enumeration is abelian, so its relabeling acts trivially
and the cell is a clearance; the three-place cell at the wiring
`[1, 0, 2]` through `[1, 2, 0]` moves the key's place from two to
one and carries the transport's own content.  The wirings, the
relabelings and the two adjugates are named once and consumed by
term. -/

/-- The relabeled wiring at a stated relabeling. -/
private def relW (k : Nat) (r x : List Nat) : List Nat :=
  (places.invPerm k r).map (fun j =>
    ground.getAt 0 r (ground.getAt 0 x j))

/-- A wiring's place in the enumeration. -/
private def idxP (k : Nat) (x : List Nat) : Nat :=
  places.idxOf x (places.perms k)

private def a2 : split.PMat := split.padj (gramWg 2)

private def a3 : split.PMat := split.padj (gramWg 3)

/-! The Gram determinant's occupancy. -/

theorem pin65 : ¬ poly.unitTail (split.pminor (gramWg 1)) := by decide +kernel

theorem pin66 : ¬ poly.unitTail (split.pminor (gramWg 2)) := by decide +kernel

theorem pin67 : ¬ poly.unitTail (split.pminor (gramWg 3)) := by decide +kernel

theorem pin68 : ¬ poly.unitTail (split.pminor (gramWg 3)) := gramWg_detOcc 3

/-! The Gram's transport symmetry at the two-place cell. -/

theorem pin69 : ground.getAt [] (ground.getAt [] (gramWg 2)
      (idxP 2 (relW 2 [1, 0] [1, 0])))
      (idxP 2 (relW 2 [1, 0] [0, 1]))
    = ground.getAt [] (ground.getAt [] (gramWg 2)
      (idxP 2 [1, 0])) (idxP 2 [0, 1]) := by decide +kernel

theorem pin70 : ground.getAt [] (ground.getAt [] (gramWg 2)
      (idxP 2 (relW 2 [1, 0] [1, 0])))
      (idxP 2 (relW 2 [1, 0] [0, 1]))
    = ground.getAt [] (ground.getAt [] (gramWg 2)
      (idxP 2 [1, 0])) (idxP 2 [0, 1]) :=
  gramWg_transport 2 [1, 0] [0, 1] [1, 0] (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The Gram's transport symmetry at the three-place cells: the
order's own pair and the moving cell. -/

theorem pin71 : ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 (relW 3 [2, 0, 1] [1, 2, 0])))
      (idxP 3 (relW 3 [2, 0, 1] [2, 0, 1]))
    = ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 [1, 2, 0])) (idxP 3 [2, 0, 1]) := by decide +kernel

theorem pin72 : ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 (relW 3 [2, 0, 1] [1, 2, 0])))
      (idxP 3 (relW 3 [2, 0, 1] [2, 0, 1]))
    = ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 [1, 2, 0])) (idxP 3 [2, 0, 1]) :=
  gramWg_transport 3 [1, 2, 0] [2, 0, 1] [2, 0, 1]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem pin73 : relW 3 [1, 2, 0] [1, 0, 2] = [0, 2, 1] := by decide +kernel

theorem pin74 : idxP 3 [1, 0, 2] = 2 := by decide +kernel

theorem pin75 : idxP 3 (relW 3 [1, 2, 0] [1, 0, 2]) = 1 := by decide +kernel

theorem pin76 : ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 (relW 3 [1, 2, 0] [1, 0, 2])))
      (idxP 3 (relW 3 [1, 2, 0] [1, 2, 0]))
    = ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 [1, 0, 2])) (idxP 3 [1, 2, 0]) := by decide +kernel

theorem pin77 : ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 (relW 3 [1, 2, 0] [1, 0, 2])))
      (idxP 3 (relW 3 [1, 2, 0] [1, 2, 0]))
    = ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 [1, 0, 2])) (idxP 3 [1, 2, 0]) :=
  gramWg_transport 3 [1, 0, 2] [1, 2, 0] [1, 2, 0]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The Weingarten column's travel at the two- and three-place
cells. -/

theorem pin78 : poly.oneValue
    (ground.getAt [] (ground.getAt [] a2
      (idxP 2 (relW 2 [1, 0] [1, 0]))) (idxP 2 (List.range 2)))
    (ground.getAt [] (ground.getAt [] a2
      (idxP 2 [1, 0])) (idxP 2 (List.range 2))) := by decide +kernel

theorem pin79 : poly.oneValue
    (ground.getAt [] (ground.getAt []
      (split.padj (gramWg 2))
      (idxP 2 (relW 2 [1, 0] [1, 0]))) (idxP 2 (List.range 2)))
    (ground.getAt [] (ground.getAt []
      (split.padj (gramWg 2))
      (idxP 2 [1, 0])) (idxP 2 (List.range 2))) :=
  wgCol_transport 2 [1, 0] [1, 0] (by decide +kernel)
    (by decide +kernel)

theorem pin80 : poly.oneValue
    (ground.getAt [] (ground.getAt [] a3
      (idxP 3 (relW 3 [2, 0, 1] [1, 2, 0]))) (idxP 3 (List.range 3)))
    (ground.getAt [] (ground.getAt [] a3
      (idxP 3 [1, 2, 0])) (idxP 3 (List.range 3))) := by decide +kernel

theorem pin81 : poly.oneValue
    (ground.getAt [] (ground.getAt []
      (split.padj (gramWg 3))
      (idxP 3 (relW 3 [2, 0, 1] [1, 2, 0]))) (idxP 3 (List.range 3)))
    (ground.getAt [] (ground.getAt []
      (split.padj (gramWg 3))
      (idxP 3 [1, 2, 0])) (idxP 3 (List.range 3))) :=
  wgCol_transport 3 [1, 2, 0] [2, 0, 1] (by decide +kernel)
    (by decide +kernel)

theorem pin82 : poly.oneValue
    (ground.getAt [] (ground.getAt [] a3
      (idxP 3 (relW 3 [1, 2, 0] [1, 0, 2]))) (idxP 3 (List.range 3)))
    (ground.getAt [] (ground.getAt [] a3
      (idxP 3 [1, 0, 2])) (idxP 3 (List.range 3))) := by decide +kernel

theorem pin83 : poly.oneValue
    (ground.getAt [] (ground.getAt []
      (split.padj (gramWg 3))
      (idxP 3 (relW 3 [1, 2, 0] [1, 0, 2]))) (idxP 3 (List.range 3)))
    (ground.getAt [] (ground.getAt []
      (split.padj (gramWg 3))
      (idxP 3 [1, 0, 2])) (idxP 3 (List.range 3))) :=
  wgCol_transport 3 [1, 0, 2] [1, 2, 0] (by decide +kernel)
    (by decide +kernel)

/-- The relabeling's membership binder is load-bearing: at the
repeated word `[0, 0, 2]` the displayed transport equality fails. -/
theorem pin84 : ¬ (ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 (relW 3 [0, 0, 2] [1, 0, 2])))
      (idxP 3 (relW 3 [0, 0, 2] [1, 2, 0]))
    = ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 [1, 0, 2])) (idxP 3 [1, 2, 0])) := by decide +kernel

/-! `rem:kernel`'s gauge-mode read at the carried evaluation: a
letter-preserving relabeling of the site and its wiring reads the
site's own value, the two crossing to the sum's unit. -/

/-- A site read at a relabeling of its places. -/
private def relSite (G : FList) (r : List Nat) : FList :=
  r.map (fun j => ground.getAt (0, false) G j)

/-- A wiring carried along a relabeling of the places. -/
private def relWire (G : FList) (r p : List Nat) : List Nat :=
  r.map (fun j => ground.getAt 0 (places.invPerm G.length r)
    (ground.getAt 0 p j))

/-- The same-site cell: the relabeling exchanges the two
undaggered places, the site reads back as itself and the carried
wiring moves. -/
theorem pin85 : relSite fUUdd [1, 0, 2, 3] = fUUdd := by decide +kernel

theorem pin86 : ¬ (relWire fUUdd [1, 0, 2, 3] [2, 3, 0, 1]
    = [2, 3, 0, 1]) := by decide +kernel

theorem pin87 : crossNull (evalPhi (relSite fUUdd [1, 0, 2, 3])
    (relWire fUUdd [1, 0, 2, 3] [2, 3, 0, 1]))
    (evalPhi fUUdd [2, 3, 0, 1]) := by decide +kernel

theorem pin88 : crossNull (evalPhi (relSite fUUdd [1, 0, 2, 3])
    (relWire fUUdd [1, 0, 2, 3] [2, 3, 0, 1]))
    (evalPhi fUUdd [2, 3, 0, 1]) :=
  evalPhi_transport fUUdd [2, 3, 0, 1] [1, 0, 2, 3]
    (by decide +kernel) (by decide +kernel)

/-- The cross-site cell: the relabeling swaps the undaggered block
against the daggered one, so both the site and the wiring move. -/
theorem pin89 : ¬ (relSite fUUdd [2, 3, 0, 1] = fUUdd) := by decide +kernel

theorem pin90 : ¬ (relWire fUUdd [2, 3, 0, 1] [1, 0, 2, 3]
    = [1, 0, 2, 3]) := by decide +kernel

theorem pin91 : crossNull (evalPhi (relSite fUUdd [2, 3, 0, 1])
    (relWire fUUdd [2, 3, 0, 1] [1, 0, 2, 3]))
    (evalPhi fUUdd [1, 0, 2, 3]) := by decide +kernel

theorem pin92 : crossNull (evalPhi (relSite fUUdd [2, 3, 0, 1])
    (relWire fUUdd [2, 3, 0, 1] [1, 0, 2, 3]))
    (evalPhi fUUdd [1, 0, 2, 3]) :=
  evalPhi_transport fUUdd [1, 0, 2, 3] [2, 3, 0, 1]
    (by decide +kernel) (by decide +kernel)

/-- The two-variable moving cell: the relabeling exchanges the
daggered `U` place with the daggered `V` place, the site moves and
the relabeling does not commute with the wiring. -/
theorem pin93 : ¬ (relSite fCyc [0, 1, 3, 2] = fCyc) := by decide +kernel

theorem pin94 : ¬ (relWire fCyc [0, 1, 3, 2] [1, 2, 3, 0]
    = [1, 2, 3, 0]) := by decide +kernel

theorem pin95 : crossNull (evalPhi (relSite fCyc [0, 1, 3, 2])
    (relWire fCyc [0, 1, 3, 2] [1, 2, 3, 0]))
    (evalPhi fCyc [1, 2, 3, 0]) := by decide +kernel

theorem pin96 : crossNull (evalPhi (relSite fCyc [0, 1, 3, 2])
    (relWire fCyc [0, 1, 3, 2] [1, 2, 3, 0]))
    (evalPhi fCyc [1, 2, 3, 0]) :=
  evalPhi_transport fCyc [1, 2, 3, 0] [0, 1, 3, 2]
    (by decide +kernel) (by decide +kernel)

/-- The wiring's membership binder is load-bearing: at the vacant
word `[0, 0, 0, 0]` the displayed cross read fails. -/
theorem pin97 : ¬ crossNull (evalPhi (relSite fUUdd [1, 0, 2, 3])
    (relWire fUUdd [1, 0, 2, 3] [0, 0, 0, 0]))
    (evalPhi fUUdd [0, 0, 0, 0]) := by decide +kernel

/-- A forged wiring passing elsewhere: at the repeated word
`[0, 0, 2, 3]` the same relabeling reads the cross null, so the
binder's refusal is the exhibited cell's. -/
theorem pin98 : crossNull (evalPhi (relSite fUUdd [1, 0, 2, 3])
    (relWire fUUdd [1, 0, 2, 3] [0, 0, 2, 3]))
    (evalPhi fUUdd [0, 0, 2, 3]) := by decide +kernel

/-- The relabeling's membership binder is load-bearing: at the
repeated word `[0, 0, 2, 3]` the displayed cross read fails. -/
theorem pin99 : ¬ crossNull (evalPhi (relSite fUUdd [0, 0, 2, 3])
    (relWire fUUdd [0, 0, 2, 3] [2, 3, 0, 1]))
    (evalPhi fUUdd [2, 3, 0, 1]) := by decide +kernel

/-! The orientation cell: the wiring travels at the pull — the
site at the relabeling's places, the wiring composed between the
partner and the relabeling — and the composition parts from its
reversal at a relabeling off its own partner.  The relabeling
`[0, 2, 3, 1]` reads off its partner, the carried wiring parts
from the reversed carriage, the pull-carried pairing reads, and
the reverse-carried pairing refuses. -/

private def relWireRev (G : FList) (r p : List Nat) : List Nat :=
  (places.invPerm G.length r).map (fun j =>
    ground.getAt 0 r (ground.getAt 0 p j))

theorem pin100 : ¬ (places.invPerm 4 [0, 2, 3, 1] = [0, 2, 3, 1]) := by
  decide +kernel
theorem pin101 : ¬ (relWire fUUdd [0, 2, 3, 1] [0, 1, 3, 2]
    = relWireRev fUUdd [0, 2, 3, 1] [0, 1, 3, 2]) := by
  decide +kernel
theorem pin102 : crossNull
    (evalPhi (relSite fUUdd [0, 2, 3, 1])
      (relWire fUUdd [0, 2, 3, 1] [0, 1, 3, 2]))
    (evalPhi fUUdd [0, 1, 3, 2]) := by decide +kernel
theorem pin103 : crossNull
    (evalPhi (relSite fUUdd [0, 2, 3, 1])
      (relWire fUUdd [0, 2, 3, 1] [0, 1, 3, 2]))
    (evalPhi fUUdd [0, 1, 3, 2]) :=
  evalPhi_transport fUUdd [0, 1, 3, 2] [0, 2, 3, 1]
    (by decide +kernel) (by decide +kernel)
theorem pin104 : ¬ crossNull
    (evalPhi (relSite fUUdd [0, 2, 3, 1])
      (relWireRev fUUdd [0, 2, 3, 1] [0, 1, 3, 2]))
    (evalPhi fUUdd [0, 1, 3, 2]) := by decide +kernel

end wg
