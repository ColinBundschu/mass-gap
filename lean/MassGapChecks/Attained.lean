import MassGap.Attained
import MassGap.Momentform
/-!
The check module for `lem:attained`: the batteries re-read the
attained edge at the free window `et3` by kernel `decide`, the
window whose located roots are `0, 12, 32` at the unit gram with
the diagonalizing congruence the identity.  At `(E₀, p, q) = (4, 3, 1)`
the edge is `12` and the root `12` sits at it.

Clause (i) is the spectral read with a named edge (`edgeRead`).  It
is decided at the window and consumed at the attainment
(`attained_at`, the composite read: the named edge's eigen column
with its two moments at equality and the first strictly above the
sum's unit), refused at a root list whose least occupied root sits
beyond the edge — the spectral read holding there, the edge
conjunct alone failing — and refused again at a root list carrying
a root at the edge while a lower occupied root sits strictly below
it — the edge conjunct holding, the spectral read alone failing.
The window's own refusal one clearing further out (`(4, 4, 1)`,
the edge `16`) is pinned beside them.

Clause (ii) is the eigen column's two moments (`moment_eq`): at the
root at the edge the column's moments read equal members at the two
clearings and the first sits strictly above the sum's unit, the
theorem's route beside the two conjuncts decided raw.  The refusal
moves to the root `32`, off the edge: the located root's edge read
fails and the equality's instance fails with it, `1024` against
`384` at the two clearings.

Clause (iii) is the weight reading.  At a vector supported on the
kernel root and the edge root the moments read equal members, and
`weights_at` puts each occupied weight at the kernel point (the
first coordinate) or at the level exactly (the second); at the edge
root's own coordinate `weight_occupied` produces the occupied
weight from a first moment strictly above the sum's unit.  The
refusals isolate the two binders: at the unit family the first
moment sits at the sum's unit while the moments still read equal
members, and the weight at the edge coordinate fails; at a vector
supported on the root `32` the moments read unequal members while
the weight there is occupied, and the root is neither at the kernel
point nor at the edge.

The packaging identities close the file: `thm:momentform`'s two
moments at the carrier ARE `lem:inertia`'s quadratic reads at the
gap and at its square, one object at every window matrix and
vector, the reads' own unfolding.

The shape binders (`sqAt`, the vector lengths, the congruence's
own reads inside `split.diagRead`) are the certificate Props'
standing shape convention and carry no refusal of their own.
-/

open ground elim inertia attained

private def u : BPair := BPair.unit

/-- The free window's gap: the located roots `0, 12, 32` on the
diagonal. -/
private def et3 : Mat :=
  [[u, u, u], [u, ⟨13, 1⟩, u], [u, u, ⟨33, 1⟩]]

/-- The diagonalizing congruence at the window: the gap is already
diagonal, so the congruence and its adjugate witness are the
identity. -/
private def id3 : SqMat 3 := ⟨idMat 3, by decide +kernel⟩

/-- The located root data, each root's scale at the sum's own
unit. -/
private def l3 : List (BPair × Pos × BPair) :=
  [(u, 1, ⟨2, 1⟩), (⟨13, 1⟩, 1, ⟨2, 1⟩), (⟨33, 1⟩, 1, ⟨2, 1⟩)]

/-- The located roots with their clearings, the root data's own
projection. -/
private def roots3 : List (BPair × Pos) :=
  [(u, 1), (⟨13, 1⟩, 1), (⟨33, 1⟩, 1)]

example : l3.map (fun r => (r.1, r.2.1)) = roots3 := by decide +kernel

/-- The certificate at the window: the identity congruence carries
the pencil to the located roots' diagonal. -/
private theorem hdP : split.diagRead et3 (idMat 3) id3 id3 l3 := by
  decide +kernel

/-- The spectral read at the edge `12`. -/
private theorem hsP : speccut.specRead roots3 4 3 1 := by decide +kernel

/-! Clause (i): the spectral read with a named edge, and the two
refusals isolating its conjuncts. -/

private theorem heP : edgeRead roots3 4 3 1 := by decide +kernel

/-- The attainment at the named edge, the composite read the
consumers cite: the edge root's eigen column with its two moments
at equality and the first strictly above the sum's unit. -/
example : ∃ j, j < 3
    ∧ ((inertia.quadForm (matMul et3 et3)
          (matVec id3.val (elim.idRow 3 j))).scale (1 : Pos)).oneValue
        ((inertia.quadForm et3
          (matVec id3.val (elim.idRow 3 j))).scale ((4 : Pos) * 3))
    ∧ BPair.unit < inertia.quadForm et3
        (matVec id3.val (elim.idRow 3 j)) :=
  attained_at et3 id3 id3 l3 4 3 1 hdP heP

/-- The refusal isolating the edge conjunct: the least occupied
root `16` sits beyond the edge `12`, so the spectral read holds
while no root is at the edge. -/
private def rootsGap : List (BPair × Pos) := [(u, 1), (⟨17, 1⟩, 1)]

example : speccut.specRead rootsGap 4 3 1 := by decide +kernel
example : ¬ edgeRead rootsGap 4 3 1 := by decide +kernel

/-- The refusal isolating the spectral read: at the edge `16` the
root `16` names it while the occupied root `12` sits strictly
below, so the edge conjunct holds and the spectral read alone
fails. -/
private def rootsAt : List (BPair × Pos) := [(⟨13, 1⟩, 1), (⟨17, 1⟩, 1)]

example : (rootsAt.any (fun r =>
    decide ((r.1.scale (1 : Pos)).oneValue
      (BPair.ofPos ((4 : Pos) * 4 * r.2))))) = true := by decide +kernel
example : ¬ speccut.specRead rootsAt 4 4 1 := by decide +kernel
example : ¬ edgeRead rootsAt 4 4 1 := by decide +kernel

/-- The window's own read one clearing further out: at the edge
`16` the root `12` sits below it and no root names it, so both
conjuncts fail. -/
example : ¬ speccut.specRead roots3 4 4 1 := by decide +kernel
example : ¬ edgeRead roots3 4 4 1 := by decide +kernel

/-! Clause (ii): the eigen column's two moments at the root at the
edge. -/

/-- The eigen column at the root at the edge, the congruence's own
second column. -/
private def y1 : List BPair := matVec id3.val (elim.idRow 3 1)

example : y1 = [u, ⟨2, 1⟩, u] := by decide +kernel

example : (inertia.quadForm et3 y1).oneValue ⟨13, 1⟩ := by decide +kernel
example : (inertia.quadForm (matMul et3 et3) y1).oneValue ⟨145, 1⟩ := by
  decide +kernel

private theorem hmom1 :
    ((inertia.quadForm (matMul et3 et3) y1).scale (1 : Pos)).oneValue
      ((inertia.quadForm et3 y1).scale ((4 : Pos) * 3)) := by decide +kernel

private theorem hpos1 : BPair.unit < inertia.quadForm et3 y1 := by
  decide +kernel

example : ((inertia.quadForm (matMul et3 et3)
      (matVec id3.val (elim.idRow 3 1))).scale (1 : Pos)).oneValue
    ((inertia.quadForm et3
      (matVec id3.val (elim.idRow 3 1))).scale ((4 : Pos) * 3))
    ∧ BPair.unit < inertia.quadForm et3
      (matVec id3.val (elim.idRow 3 1)) :=
  moment_eq et3 id3 id3 l3 4 3 1 hdP 1 (by decide +kernel)
    ⟨13, 1⟩ ⟨2, 1⟩ 1 rfl (by decide +kernel)

/-- The refusal isolating `hedge`: at the root `32` the located
root is off the edge `12` and the equality's own instance fails
with it, `1024` against `384` at the two clearings, every other
binder holding. -/
private def y2 : List BPair := matVec id3.val (elim.idRow 3 2)

example : ground.getAt (BPair.unit, Pos.one, BPair.unit) l3 2
    = (⟨33, 1⟩, (1 : Pos), ⟨2, 1⟩) := rfl
example : ¬ ((⟨33, 1⟩ : BPair).scale (1 : Pos)).oneValue
    (BPair.ofPos ((4 : Pos) * 3 * 1)) := by decide +kernel
example : (inertia.quadForm (matMul et3 et3) y2).oneValue ⟨1025, 1⟩ := by
  decide +kernel
example : ((inertia.quadForm et3 y2).scale ((4 : Pos) * 3)).oneValue
    ⟨385, 1⟩ := by decide +kernel
example : ¬ ((inertia.quadForm (matMul et3 et3) y2).scale (1 : Pos)).oneValue
    ((inertia.quadForm et3 y2).scale ((4 : Pos) * 3)) := by decide +kernel

/-! Clause (iii): the weight reading at the located roots. -/

/-- A vector supported on the kernel root and the root at the
edge. -/
private def yK : List BPair := [⟨2, 1⟩, ⟨2, 1⟩, u]

example : (inertia.quadForm et3 yK).oneValue ⟨13, 1⟩ := by decide +kernel
example : (inertia.quadForm (matMul et3 et3) yK).oneValue ⟨145, 1⟩ := by
  decide +kernel

/-- The moments read equal members at the two clearings there. -/
private theorem hmomK :
    ((inertia.quadForm (matMul et3 et3) yK).scale (1 : Pos)).oneValue
      ((inertia.quadForm et3 yK).scale ((4 : Pos) * 3)) := by decide +kernel

example : ((u : BPair).oneValue BPair.unit)
    ∨ ((u : BPair).scale (1 : Pos)).oneValue
      (BPair.ofPos ((4 : Pos) * 3 * 1)) := by decide +kernel

example : ((u : BPair).oneValue BPair.unit)
    ∨ ((u : BPair).scale (1 : Pos)).oneValue
      (BPair.ofPos ((4 : Pos) * 3 * 1)) :=
  weights_at et3 id3 id3 l3 4 3 1 hdP hsP yK (by decide +kernel)
    hmomK 0 (by decide +kernel) u ⟨2, 1⟩ 1 rfl (by decide +kernel)

example : ((⟨13, 1⟩ : BPair).oneValue BPair.unit)
    ∨ ((⟨13, 1⟩ : BPair).scale (1 : Pos)).oneValue
      (BPair.ofPos ((4 : Pos) * 3 * 1)) := by decide +kernel

example : ((⟨13, 1⟩ : BPair).oneValue BPair.unit)
    ∨ ((⟨13, 1⟩ : BPair).scale (1 : Pos)).oneValue
      (BPair.ofPos ((4 : Pos) * 3 * 1)) :=
  weights_at et3 id3 id3 l3 4 3 1 hdP hsP yK (by decide +kernel)
    hmomK 1 (by decide +kernel) ⟨13, 1⟩ ⟨2, 1⟩ 1 rfl (by decide +kernel)

/-- The refusal isolating the occupied weight: at the vector on the
kernel and edge roots the moments read equal members while the
third coordinate's weight sits at the sum's unit, and the root
`32`'s disjunction is the refused conclusion, its pin the `hmom`
refusal's below. -/
example : ¬ (BPair.unit < (ground.getAt BPair.unit (matVec id3.val yK) 2
    * ground.getAt BPair.unit (matVec id3.val yK) 2)
    * (⟨2, 1⟩ * BPair.ofPos (1 : Pos))) := by decide +kernel

/-- The refusal isolating `hmom`: at a vector supported on the root
`32` the two moments read unequal members while the weight at that
coordinate is occupied, and the root is neither at the kernel point
nor at the edge. -/
private def yBad : List BPair := [u, u, ⟨2, 1⟩]

example : ¬ ((inertia.quadForm (matMul et3 et3) yBad).scale (1 : Pos)).oneValue
    ((inertia.quadForm et3 yBad).scale ((4 : Pos) * 3)) := by decide +kernel
example : BPair.unit < (ground.getAt BPair.unit (matVec id3.val yBad) 2
    * ground.getAt BPair.unit (matVec id3.val yBad) 2)
    * (⟨2, 1⟩ * BPair.ofPos (1 : Pos)) := by decide +kernel
example : ¬ (((⟨33, 1⟩ : BPair).oneValue BPair.unit)
    ∨ ((⟨33, 1⟩ : BPair).scale (1 : Pos)).oneValue
      (BPair.ofPos ((4 : Pos) * 3 * 1))) := by decide +kernel

example : ground.getAt (BPair.unit, Pos.one, BPair.unit) l3 1
      = (⟨13, 1⟩, (1 : Pos), ⟨2, 1⟩)
    ∧ ((⟨13, 1⟩ : BPair).scale (1 : Pos)).oneValue
      (BPair.ofPos ((4 : Pos) * 3 * 1))
    ∧ BPair.unit < (ground.getAt BPair.unit (matVec id3.val y1) 1
        * ground.getAt BPair.unit (matVec id3.val y1) 1)
        * (⟨2, 1⟩ * BPair.ofPos (1 : Pos)) := by decide +kernel

example : ∃ j, j < 3 ∧ ∃ nj gj : BPair, ∃ dj : Pos,
    ground.getAt (BPair.unit, Pos.one, BPair.unit) l3 j = (nj, dj, gj)
    ∧ (nj.scale (1 : Pos)).oneValue (BPair.ofPos ((4 : Pos) * 3 * dj))
    ∧ BPair.unit < (ground.getAt BPair.unit (matVec id3.val y1) j
        * ground.getAt BPair.unit (matVec id3.val y1) j)
        * (gj * BPair.ofPos dj) :=
  weight_occupied et3 id3 id3 l3 4 3 1 hdP hsP y1 (by decide +kernel)
    hmom1 hpos1

/-- The refusal isolating `hpos`: at the unit family the two
moments still read equal members while the first moment sits at the
sum's unit, and the weight at the edge coordinate fails. -/
private def yU : List BPair := [u, u, u]

example : ((inertia.quadForm (matMul et3 et3) yU).scale (1 : Pos)).oneValue
    ((inertia.quadForm et3 yU).scale ((4 : Pos) * 3)) := by decide +kernel
example : ¬ (BPair.unit < inertia.quadForm et3 yU) := by decide +kernel
example : ¬ (BPair.unit < (ground.getAt BPair.unit (matVec id3.val yU) 1
    * ground.getAt BPair.unit (matVec id3.val yU) 1)
    * (⟨2, 1⟩ * BPair.ofPos (1 : Pos))) := by decide +kernel
example : ¬ ((u : BPair).scale (1 : Pos)).oneValue
    (BPair.ofPos ((4 : Pos) * 3 * 1)) := by decide +kernel

/-- The refusal isolating `hmom` in the occupancy read: at the
vector supported on the root `32` the first moment is strictly
above the sum's unit while the moments read unequal members, and
the located root at that coordinate is off the edge. -/
example : BPair.unit < inertia.quadForm et3 yBad := by decide +kernel
example : ¬ (BPair.unit < (ground.getAt BPair.unit (matVec id3.val yBad) 1
    * ground.getAt BPair.unit (matVec id3.val yBad) 1)
    * (⟨2, 1⟩ * BPair.ofPos (1 : Pos))) := by decide +kernel

/-! The refusal isolating the spectral read in the weight clauses:
a two-key window whose lower root `6` sits strictly between the
kernel point and the edge `12`.  The certificate and the moments'
equal members hold at the stated vector — `μ₁ = 240` against
`μ₂ = 2880` at the clearings — while the spectral read fails, the
weights at both coordinates are occupied, and neither root reads
the kernel point or the edge: `weights_at`'s disjunction refuses at
the first key and `weight_occupied`'s occupancy at both. -/

private def et2 : Mat := [[⟨7, 1⟩, u], [u, ⟨17, 1⟩]]

private def id2 : SqMat 2 := ⟨inertia.idMat 2, by decide +kernel⟩

private def l2 : List (BPair × Pos × BPair) :=
  [(⟨7, 1⟩, 1, ⟨2, 1⟩), (⟨17, 1⟩, 1, ⟨2, 1⟩)]

private def y2v : List BPair := [⟨5, 1⟩, ⟨4, 1⟩]

example : split.diagRead et2 (inertia.idMat 2) id2 id2 l2 := by
  decide +kernel
example : ¬ speccut.specRead (l2.map (fun r => (r.1, r.2.1))) 4 3 1 := by
  decide +kernel
example : ((inertia.quadForm (matMul et2 et2) y2v).scale (1 : Pos)).oneValue
    ((inertia.quadForm et2 y2v).scale ((4 : Pos) * 3)) := by decide +kernel
example : BPair.unit < inertia.quadForm et2 y2v := by decide +kernel
example : BPair.unit < (ground.getAt BPair.unit (matVec id2.val y2v) 0
    * ground.getAt BPair.unit (matVec id2.val y2v) 0)
    * (⟨2, 1⟩ * BPair.ofPos (1 : Pos)) := by decide +kernel
example : ¬ (((⟨7, 1⟩ : BPair).oneValue BPair.unit)
    ∨ ((⟨7, 1⟩ : BPair).scale (1 : Pos)).oneValue
      (BPair.ofPos ((4 : Pos) * 3 * 1))) := by decide +kernel
example : ¬ ((⟨17, 1⟩ : BPair).scale (1 : Pos)).oneValue
    (BPair.ofPos ((4 : Pos) * 3 * 1)) := by decide +kernel

/-! The moments' packaging: `thm:momentform`'s two reads at the
carrier are the quadratic reads at the gap and at its square. -/

example {n : Nat} (E : SqMat n) (Y : Vec n) :
    momentform.mu1 E Y = inertia.quadForm E.val Y.val := rfl
example {n : Nat} (E : SqMat n) (Y : Vec n) :
    momentform.mu2 E Y = inertia.quadForm (matMul E.val E.val) Y.val := rfl

/-! Clause (iv): the probe cap at the eigen column of the root `12`
against the level `16`, the pair `(144 : 16·12)` on its lower side
refusing the spectral read there, the theorem route beside the
decided refusal; and the isolating refusal of the pair binder: at
the level `12` the pair reads equal members, the spectral read
holding. -/

private def sp16 : Split 3 :=
  mkSplit 3 (siteDatum (matScale (1 : Pos) (matMul et3 et3))
    (matScale ((4 : Pos) * 4) et3))

private theorem hsp16 : splitRead (siteDatum
    (matScale (1 : Pos) (matMul et3 et3)) (matScale ((4 : Pos) * 4) et3)) sp16 :=
  mkSplit_read 3 _ (by decide +kernel) (by decide +kernel)

example : (inertia.quadForm (matMul et3 et3) y1).scale (1 : Pos)
    < (inertia.quadForm et3 y1).scale ((4 : Pos) * 4) := by decide +kernel
example : ¬ speccut.specRead (l3.map (fun r => (r.1, r.2.1))) 4 4 1 :=
  probe_cap et3 id3 id3 l3 4 4 1 hdP sp16 hsp16 y1 (by decide +kernel)
    (by decide +kernel)
example : ¬ ((inertia.quadForm (matMul et3 et3) y1).scale (1 : Pos)
    < (inertia.quadForm et3 y1).scale ((4 : Pos) * 3)) := by decide +kernel
