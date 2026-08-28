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
the fold.  The transport tier closes the module: the Gram
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

private def a2 : split.PMat := genericlift.padj (gramWg 2)

private def a3 : split.PMat := genericlift.padj (gramWg 3)

/-! The Gram determinant's occupancy. -/

example : ¬ poly.unitTail (split.pminor (gramWg 1)) := by decide +kernel

example : ¬ poly.unitTail (split.pminor (gramWg 2)) := by decide +kernel

example : ¬ poly.unitTail (split.pminor (gramWg 3)) := by decide +kernel

example : ¬ poly.unitTail (split.pminor (gramWg 3)) := gramWg_detOcc 3

/-! The Gram's transport symmetry at the two-place cell. -/

example : ground.getAt [] (ground.getAt [] (gramWg 2)
      (idxP 2 (relW 2 [1, 0] [1, 0])))
      (idxP 2 (relW 2 [1, 0] [0, 1]))
    = ground.getAt [] (ground.getAt [] (gramWg 2)
      (idxP 2 [1, 0])) (idxP 2 [0, 1]) := by decide +kernel

example : ground.getAt [] (ground.getAt [] (gramWg 2)
      (idxP 2 (relW 2 [1, 0] [1, 0])))
      (idxP 2 (relW 2 [1, 0] [0, 1]))
    = ground.getAt [] (ground.getAt [] (gramWg 2)
      (idxP 2 [1, 0])) (idxP 2 [0, 1]) :=
  gramWg_transport 2 [1, 0] [0, 1] [1, 0] (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The Gram's transport symmetry at the three-place cells: the
order's own pair and the moving cell. -/

example : ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 (relW 3 [2, 0, 1] [1, 2, 0])))
      (idxP 3 (relW 3 [2, 0, 1] [2, 0, 1]))
    = ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 [1, 2, 0])) (idxP 3 [2, 0, 1]) := by decide +kernel

example : ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 (relW 3 [2, 0, 1] [1, 2, 0])))
      (idxP 3 (relW 3 [2, 0, 1] [2, 0, 1]))
    = ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 [1, 2, 0])) (idxP 3 [2, 0, 1]) :=
  gramWg_transport 3 [1, 2, 0] [2, 0, 1] [2, 0, 1]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : relW 3 [1, 2, 0] [1, 0, 2] = [0, 2, 1] := by decide +kernel

example : idxP 3 [1, 0, 2] = 2 := by decide +kernel

example : idxP 3 (relW 3 [1, 2, 0] [1, 0, 2]) = 1 := by decide +kernel

example : ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 (relW 3 [1, 2, 0] [1, 0, 2])))
      (idxP 3 (relW 3 [1, 2, 0] [1, 2, 0]))
    = ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 [1, 0, 2])) (idxP 3 [1, 2, 0]) := by decide +kernel

example : ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 (relW 3 [1, 2, 0] [1, 0, 2])))
      (idxP 3 (relW 3 [1, 2, 0] [1, 2, 0]))
    = ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 [1, 0, 2])) (idxP 3 [1, 2, 0]) :=
  gramWg_transport 3 [1, 0, 2] [1, 2, 0] [1, 2, 0]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The Weingarten column's travel at the two- and three-place
cells. -/

example : poly.oneValue
    (ground.getAt [] (ground.getAt [] a2
      (idxP 2 (relW 2 [1, 0] [1, 0]))) (idxP 2 (List.range 2)))
    (ground.getAt [] (ground.getAt [] a2
      (idxP 2 [1, 0])) (idxP 2 (List.range 2))) := by decide +kernel

example : poly.oneValue
    (ground.getAt [] (ground.getAt []
      (genericlift.padj (gramWg 2))
      (idxP 2 (relW 2 [1, 0] [1, 0]))) (idxP 2 (List.range 2)))
    (ground.getAt [] (ground.getAt []
      (genericlift.padj (gramWg 2))
      (idxP 2 [1, 0])) (idxP 2 (List.range 2))) :=
  wgCol_transport 2 [1, 0] [1, 0] (by decide +kernel)
    (by decide +kernel)

example : poly.oneValue
    (ground.getAt [] (ground.getAt [] a3
      (idxP 3 (relW 3 [2, 0, 1] [1, 2, 0]))) (idxP 3 (List.range 3)))
    (ground.getAt [] (ground.getAt [] a3
      (idxP 3 [1, 2, 0])) (idxP 3 (List.range 3))) := by decide +kernel

example : poly.oneValue
    (ground.getAt [] (ground.getAt []
      (genericlift.padj (gramWg 3))
      (idxP 3 (relW 3 [2, 0, 1] [1, 2, 0]))) (idxP 3 (List.range 3)))
    (ground.getAt [] (ground.getAt []
      (genericlift.padj (gramWg 3))
      (idxP 3 [1, 2, 0])) (idxP 3 (List.range 3))) :=
  wgCol_transport 3 [1, 2, 0] [2, 0, 1] (by decide +kernel)
    (by decide +kernel)

example : poly.oneValue
    (ground.getAt [] (ground.getAt [] a3
      (idxP 3 (relW 3 [1, 2, 0] [1, 0, 2]))) (idxP 3 (List.range 3)))
    (ground.getAt [] (ground.getAt [] a3
      (idxP 3 [1, 0, 2])) (idxP 3 (List.range 3))) := by decide +kernel

example : poly.oneValue
    (ground.getAt [] (ground.getAt []
      (genericlift.padj (gramWg 3))
      (idxP 3 (relW 3 [1, 2, 0] [1, 0, 2]))) (idxP 3 (List.range 3)))
    (ground.getAt [] (ground.getAt []
      (genericlift.padj (gramWg 3))
      (idxP 3 [1, 0, 2])) (idxP 3 (List.range 3))) :=
  wgCol_transport 3 [1, 0, 2] [1, 2, 0] (by decide +kernel)
    (by decide +kernel)

/-- The relabeling's membership binder is load-bearing: at the
repeated word `[0, 0, 2]` the displayed transport equality fails. -/
example : ¬ (ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 (relW 3 [0, 0, 2] [1, 0, 2])))
      (idxP 3 (relW 3 [0, 0, 2] [1, 2, 0]))
    = ground.getAt [] (ground.getAt [] (gramWg 3)
      (idxP 3 [1, 0, 2])) (idxP 3 [1, 2, 0])) := by decide +kernel

/-! `rem:kernel`'s gauge-mode read at the carried evaluation: a
letter-preserving relabeling of the site and its wiring reads the
site's own value, the two crossing to the sum's unit. -/

/-- A site read at a relabeling of its places. -/
private def relSite (G : FList) (r : List Nat) : FList :=
  r.map (fun j => ground.getAt (false, false) G j)

/-- A wiring carried along a relabeling of the places. -/
private def relWire (G : FList) (r p : List Nat) : List Nat :=
  r.map (fun j => ground.getAt 0 (places.invPerm G.length r)
    (ground.getAt 0 p j))

/-- The same-site cell: the relabeling exchanges the two
undaggered places, the site reads back as itself and the carried
wiring moves. -/
example : relSite fUUdd [1, 0, 2, 3] = fUUdd := by decide +kernel

example : ¬ (relWire fUUdd [1, 0, 2, 3] [2, 3, 0, 1]
    = [2, 3, 0, 1]) := by decide +kernel

example : crossNull (evalPhi (relSite fUUdd [1, 0, 2, 3])
    (relWire fUUdd [1, 0, 2, 3] [2, 3, 0, 1]))
    (evalPhi fUUdd [2, 3, 0, 1]) := by decide +kernel

example : crossNull (evalPhi (relSite fUUdd [1, 0, 2, 3])
    (relWire fUUdd [1, 0, 2, 3] [2, 3, 0, 1]))
    (evalPhi fUUdd [2, 3, 0, 1]) :=
  evalPhi_transport fUUdd [2, 3, 0, 1] [1, 0, 2, 3]
    (by decide +kernel) (by decide +kernel)

/-- The cross-site cell: the relabeling swaps the undaggered block
against the daggered one, so both the site and the wiring move. -/
example : ¬ (relSite fUUdd [2, 3, 0, 1] = fUUdd) := by decide +kernel

example : ¬ (relWire fUUdd [2, 3, 0, 1] [1, 0, 2, 3]
    = [1, 0, 2, 3]) := by decide +kernel

example : crossNull (evalPhi (relSite fUUdd [2, 3, 0, 1])
    (relWire fUUdd [2, 3, 0, 1] [1, 0, 2, 3]))
    (evalPhi fUUdd [1, 0, 2, 3]) := by decide +kernel

example : crossNull (evalPhi (relSite fUUdd [2, 3, 0, 1])
    (relWire fUUdd [2, 3, 0, 1] [1, 0, 2, 3]))
    (evalPhi fUUdd [1, 0, 2, 3]) :=
  evalPhi_transport fUUdd [1, 0, 2, 3] [2, 3, 0, 1]
    (by decide +kernel) (by decide +kernel)

/-- The two-variable moving cell: the relabeling exchanges the
daggered `U` place with the daggered `V` place, the site moves and
the relabeling does not commute with the wiring. -/
example : ¬ (relSite fCyc [0, 1, 3, 2] = fCyc) := by decide +kernel

example : ¬ (relWire fCyc [0, 1, 3, 2] [1, 2, 3, 0]
    = [1, 2, 3, 0]) := by decide +kernel

example : crossNull (evalPhi (relSite fCyc [0, 1, 3, 2])
    (relWire fCyc [0, 1, 3, 2] [1, 2, 3, 0]))
    (evalPhi fCyc [1, 2, 3, 0]) := by decide +kernel

example : crossNull (evalPhi (relSite fCyc [0, 1, 3, 2])
    (relWire fCyc [0, 1, 3, 2] [1, 2, 3, 0]))
    (evalPhi fCyc [1, 2, 3, 0]) :=
  evalPhi_transport fCyc [1, 2, 3, 0] [0, 1, 3, 2]
    (by decide +kernel) (by decide +kernel)

/-- The wiring's membership binder is load-bearing: at the vacant
word `[0, 0, 0, 0]` the displayed cross read fails. -/
example : ¬ crossNull (evalPhi (relSite fUUdd [1, 0, 2, 3])
    (relWire fUUdd [1, 0, 2, 3] [0, 0, 0, 0]))
    (evalPhi fUUdd [0, 0, 0, 0]) := by decide +kernel

/-- A forged wiring passing elsewhere: at the repeated word
`[0, 0, 2, 3]` the same relabeling reads the cross null, so the
binder's refusal is the exhibited cell's. -/
example : crossNull (evalPhi (relSite fUUdd [1, 0, 2, 3])
    (relWire fUUdd [1, 0, 2, 3] [0, 0, 2, 3]))
    (evalPhi fUUdd [0, 0, 2, 3]) := by decide +kernel

/-- The relabeling's membership binder is load-bearing: at the
repeated word `[0, 0, 2, 3]` the displayed cross read fails. -/
example : ¬ crossNull (evalPhi (relSite fUUdd [0, 0, 2, 3])
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

example : ¬ (places.invPerm 4 [0, 2, 3, 1] = [0, 2, 3, 1]) := by
  decide +kernel
example : ¬ (relWire fUUdd [0, 2, 3, 1] [0, 1, 3, 2]
    = relWireRev fUUdd [0, 2, 3, 1] [0, 1, 3, 2]) := by
  decide +kernel
example : crossNull
    (evalPhi (relSite fUUdd [0, 2, 3, 1])
      (relWire fUUdd [0, 2, 3, 1] [0, 1, 3, 2]))
    (evalPhi fUUdd [0, 1, 3, 2]) := by decide +kernel
example : crossNull
    (evalPhi (relSite fUUdd [0, 2, 3, 1])
      (relWire fUUdd [0, 2, 3, 1] [0, 1, 3, 2]))
    (evalPhi fUUdd [0, 1, 3, 2]) :=
  evalPhi_transport fUUdd [0, 1, 3, 2] [0, 2, 3, 1]
    (by decide +kernel) (by decide +kernel)
example : ¬ crossNull
    (evalPhi (relSite fUUdd [0, 2, 3, 1])
      (relWireRev fUUdd [0, 2, 3, 1] [0, 1, 3, 2]))
    (evalPhi fUUdd [0, 1, 3, 2]) := by decide +kernel
