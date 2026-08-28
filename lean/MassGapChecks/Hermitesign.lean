import MassGap.Hermitesign
/-!
The check module for `lem:hermitesign`: the batteries re-read the
pairing counts by kernel `decide` at `S = (z-1)(z-2)`.  The pairing
`H₁ = [[2,3],[3,5]]` with the trace routes' coherence
(`traceM ∘ remMulMat` against `traceRem`); the definite block's
additive identity at `z² + 1`, settled at the three remainders `1`,
`x`, `1 + x` with a general fourth; the segment count `2` on
`[0, 3]` at the unit weight; and the located sign at the isolated
`√`-free bracket `(351/352, 353/352)` of the root `1` — `p = z` on
its upper side and `p = z - 3` on its lower, each at its two splits
and closing identity, with the exchanged-identity refusals. -/
set_option maxHeartbeats 4000000

open ground poly elim inertia hermitesign

private def u : BPair := BPair.unit

/-- `S = z² - 3z + 2`, the below-top list. -/
private def sQ : Poly := [⟨3, 1⟩, ⟨1, 4⟩]

/-! The pairing `H₁ = [[2,3],[3,5]]`, and the trace routes'
coherence at `x³`. -/

example : matOneValue (hermite sQ poly.one)
    [[⟨3, 1⟩, ⟨4, 1⟩], [⟨4, 1⟩, ⟨6, 1⟩]] := by decide +kernel
example : (traceM (remMulMat sQ [u, u, u, ⟨2, 1⟩])).oneValue
    (traceRem sQ [u, u, u, ⟨2, 1⟩]) := by decide +kernel

/-! The definite block's identity at `z² + 1` (gap `4`): the three
remainders and a general fourth. -/

example : defBlockRead ⟨u, ⟨2, 1⟩, ⟨5, 1⟩⟩ ⟨2, 1⟩ u := by decide +kernel
example : defBlockRead ⟨u, ⟨2, 1⟩, ⟨5, 1⟩⟩ u ⟨2, 1⟩ := by decide +kernel
example : defBlockRead ⟨u, ⟨2, 1⟩, ⟨5, 1⟩⟩ ⟨2, 1⟩ ⟨2, 1⟩ := by decide +kernel
example : defBlockRead ⟨u, ⟨2, 1⟩, ⟨5, 1⟩⟩ ⟨3, 1⟩ ⟨4, 1⟩ := by decide +kernel

/-! The segment count `2` on `[0, 3]`: `H₁` positive definite at
`diag(2, 2)`, the pencil at `diag(-4, -16)`. -/

private def spH1 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 4⟩], [⟨1, 1⟩, ⟨3, 1⟩]], rfl⟩,
   ⟨[[⟨3, 1⟩, ⟨4, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨3, 1⟩, .one ⟨3, 1⟩], 0, rfl⟩
private def spB03 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨7, 1⟩], [⟨1, 1⟩, ⟨1, 5⟩]], rfl⟩,
   ⟨[[⟨1, 5⟩, ⟨1, 7⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨1, 5⟩, .one ⟨1, 17⟩], 0, rfl⟩

example : segCountRead sQ u ⟨4, 1⟩ 1 2 spH1 spB03 := by decide +kernel

/-! The located sign at the bracket `(351/352, 353/352)` of the
root `1`, width `[2 : 352]` at half the separation: `p = z` on its
upper side (`H_p = [[3,5],[5,9]]` positive definite, the pencil at
one reversal), `p = z - 3` on its lower (`H_p` negative definite,
the pencil at one reversal), and the exchanged identities
refused. -/

private def spHx : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 6⟩], [⟨1, 1⟩, ⟨4, 1⟩]], rfl⟩,
   ⟨[[⟨4, 1⟩, ⟨6, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨4, 1⟩, .one ⟨7, 1⟩], 0, rfl⟩
private def spBx : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 495612⟩], [⟨1, 1⟩, ⟨247806, 1⟩]], rfl⟩,
   ⟨[[⟨247806, 1⟩, ⟨495612, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨247806, 1⟩, .one ⟨1, 61407565831⟩], 0, rfl⟩

example : sideUpperRead sQ [u, ⟨2, 1⟩] ⟨352, 1⟩ ⟨354, 1⟩ 352 2 352
    spHx spBx := by decide +kernel
example : ¬ sideLowerRead sQ [u, ⟨2, 1⟩] ⟨352, 1⟩ ⟨354, 1⟩ 352 2 352
    spHx spBx := by decide +kernel

private def spHm : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨5, 1⟩], [⟨1, 1⟩, ⟨1, 4⟩]], rfl⟩,
   ⟨[[⟨1, 4⟩, ⟨1, 5⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨1, 4⟩, .one ⟨1, 7⟩], 0, rfl⟩
private def spBm : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨247805, 1⟩], [⟨1, 1⟩, ⟨1, 123902⟩]], rfl⟩,
   ⟨[[⟨1, 123902⟩, ⟨1, 247805⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨1, 123902⟩, .one ⟨30703411207, 1⟩], 0, rfl⟩

example : sideLowerRead sQ [⟨1, 4⟩, ⟨2, 1⟩] ⟨352, 1⟩ ⟨354, 1⟩ 352
    2 352 spHm spBm := by decide +kernel
example : ¬ sideUpperRead sQ [⟨1, 4⟩, ⟨2, 1⟩] ⟨352, 1⟩ ⟨354, 1⟩ 352
    2 352 spHm spBm := by decide +kernel
