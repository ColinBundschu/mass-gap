import MassGap.Speccut
/-!
The check module for `lem:speccut`: the batteries re-read the
spectral tie at the free window by kernel `decide` — the gap's
pencil factorizes at the located roots `0, 12, 32` (`chiRead`
against the unit gram), the spectral read holds at the member
floor's edge and is refused beyond, and the tie conjoins the
factorization, the spectral read, and the cut's split at the one
window — the spectral read the cut's own object.

The identification's forward direction rides at the same window:
the diagonalizing congruence is the identity there (the gap is
already diagonal, the scales at the sum's own unit), `spec_to_cut`
prices the cut's split at the edge and the kernel decides the same
reversal count raw, and beyond the edge the refusal bites — the
root `12` below `E₀ p = 16` and the cut's own split at that window
counting a reversal, the spectral read load-bearing.

The reading back rides at the same window: the gap `et3` carries
its own positive-semidefinite split — the floor datum, `ε₀ G + Ẽ = H`
at the floor — and `cut_to_spec` reads the located spectrum off the
cut's split there, beside the same read decided raw.

The floor datum's committed refusal closes the file: at a
one-letter window whose gap is the negative unit every other clause
holds — the congruence diagonalizes, the cut's pair is positive
semidefinite — while the spectral read fails outright, a strictly
negative level pricing `q ε² ≥ E₀ p ε` on its upper side; the gap's
own split there counts a reversal, so every split's count reads it
(`lem:inertia`'s shared count): the floor datum is the violated
clause.
-/
set_option maxHeartbeats 4000000

open ground elim inertia speccut

private def u : BPair := BPair.unit

private def et3 : Mat :=
  [[u, u, u], [u, ⟨13, 1⟩, u], [u, u, ⟨33, 1⟩]]

private def rot3 : Mat :=
  [[u, ⟨2, 1⟩, u], [u, u, ⟨2, 1⟩], [⟨2, 1⟩, u, u]]

/-- The rotation's adjugate, the inverse rotation at the unit
determinant. -/
private def rot3w : Mat :=
  [[u, u, ⟨2, 1⟩], [⟨2, 1⟩, u, u], [u, ⟨2, 1⟩, u]]

private def roots3 : List (BPair × Pos) :=
  [(u, 1), (⟨13, 1⟩, 1), (⟨33, 1⟩, 1)]

/-! The factorization at the located roots, and the spectral read
at the edge with its refusal beyond. -/

example : split.chiRead et3 (idMat 3) roots3 := by decide +kernel
example : specRead roots3 4 3 1 := by decide +kernel
example : ¬ specRead roots3 4 4 1 := by decide +kernel

/-! The tie at the window: the factorization, the spectral read,
and the cut's split at once. -/

private def spCut : Split 3 :=
  ⟨⟨rot3, by decide +kernel⟩, ⟨rot3w, by decide +kernel⟩, [.one ⟨641, 1⟩], 2, rfl⟩

example : cutTie et3 roots3 4 3 1 spCut := by decide +kernel

/-! The diagonalizing congruence at the window: the gap is already
diagonal, so the congruence is the identity and the located roots
carry the sum's own unit as their scales. -/

private def id3 : SqMat 3 := ⟨idMat 3, by decide +kernel⟩

private def l3 : List (BPair × Pos × BPair) :=
  [(u, 1, ⟨2, 1⟩), (⟨13, 1⟩, 1, ⟨2, 1⟩), (⟨33, 1⟩, 1, ⟨2, 1⟩)]

example : l3.map (fun r => (r.1, r.2.1)) = roots3 := by decide +kernel
example : split.diagRead et3 (idMat 3) id3 id3 l3 := by decide +kernel

/-! The forward direction at the window: the spectral read at the
edge prices the cut's split, the kernel deciding the same count
raw. -/

example : psdAt spCut :=
  spec_to_cut et3 id3 id3 l3 4 3 1 (by decide +kernel) (by decide +kernel)
    spCut (by decide +kernel)

example : psdAt spCut := by decide +kernel

/-! The reading back at the same window: the gap's own floor datum
is the diagonal's split (the two occupied levels in their blocks,
the kernel point trailing), and the cut's split reads the located
spectrum off it. -/

private def spGap : Split 3 :=
  ⟨⟨rot3w, by decide +kernel⟩, ⟨rot3, by decide +kernel⟩,
    [.one ⟨13, 1⟩, .one ⟨33, 1⟩], 1, rfl⟩

example : splitRead et3 spGap := by decide +kernel
example : psdAt spGap := by decide +kernel

example : specRead (l3.map (fun r => (r.1, r.2.1))) 4 3 1 :=
  cut_to_spec et3 id3 id3 l3 4 3 1 (by decide +kernel) spGap
    (by decide +kernel) (by decide +kernel) spCut (by decide +kernel) (by decide +kernel)

example : specRead (l3.map (fun r => (r.1, r.2.1))) 4 3 1 := by decide +kernel

/-! The refusal isolating the spectral read: beyond the edge the
root `12` sits below `E₀ p = 16`, and the cut's own split at that
window counts a reversal — the read load-bearing. -/

private def spBeyond : Split 3 :=
  ⟨⟨rot3w, by decide +kernel⟩, ⟨rot3, by decide +kernel⟩,
    [.one ⟨1, 49⟩, .one ⟨513, 1⟩], 1, rfl⟩

example : ¬ specRead (l3.map (fun r => (r.1, r.2.1))) 4 4 1 := by decide +kernel

example : splitRead (siteDatum (matScale (1 : Pos) (matMul et3 et3))
    (matScale ((4 : Pos) * 4) et3)) spBeyond := by decide +kernel

example : ¬ psdAt spBeyond := by decide +kernel

/-! The floor datum's committed refusal: the one-letter window at
the negative unit.  The gap is symmetric and diagonalized at the
root `-1` with its scale on the upper side, the cut's pair
`(q Ẽ² : E₀ p Ẽ)` is positive semidefinite at the split below, and
the spectral read fails — the level is off the kernel point and
strictly below the edge.  The clause the window violates is the
gap's own floor datum, and only that one. -/

private def et1 : Mat := [[⟨1, 2⟩]]

private def t1 : SqMat 1 := ⟨[[⟨3, 1⟩]], by decide +kernel⟩

private def t1w : SqMat 1 := ⟨[[⟨2, 1⟩]], by decide +kernel⟩

private def l1 : List (BPair × Pos × BPair) := [(⟨1, 2⟩, 1, ⟨5, 1⟩)]

private def sp1 : Split 1 :=
  ⟨⟨[[⟨3, 1⟩]], by decide +kernel⟩, ⟨[[⟨2, 1⟩]], by decide +kernel⟩, [.one ⟨9, 1⟩], 0, rfl⟩

example : split.diagRead et1 (idMat 1) t1 t1w l1 := by decide +kernel

example : splitRead (siteDatum (matScale (1 : Pos) (matMul et1 et1))
    (matScale ((1 : Pos) * 1) et1)) sp1 := by decide +kernel

example : psdAt sp1 := by decide +kernel

example : ¬ specRead (l1.map (fun r => (r.1, r.2.1))) 1 1 1 := by decide +kernel

/-- The gap's own split at that window: the level gap is the
negative unit, so the split counts a reversal — `cut_to_spec`'s
floor datum is what the window refuses, every clause above
holding. -/
private def spGap1 : Split 1 :=
  ⟨⟨[[⟨3, 1⟩]], by decide +kernel⟩, ⟨[[⟨2, 1⟩]], by decide +kernel⟩,
    [.one ⟨1, 5⟩], 0, rfl⟩

example : splitRead et1 spGap1 := by decide +kernel
example : ¬ psdAt spGap1 := by decide +kernel
