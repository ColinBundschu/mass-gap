import MassGap.Lap
/-!
The check module for `prop:lap`: the batteries re-read the
insertion identity's instances by kernel `decide` at the word
index's combination equality — `Δ_U tr U = c_f tr U`; the unit the
kernel point at the presentation `1 = [1 : d_f] tr(U U†)`;
`Δ_U χ_adj = d_f χ_adj` at
`χ_adj = |tr U|² - [1 : d_f] tr(U U†)`; and the graded squares
`d_f Δ_U s + 2s = d_f (d_f + 1) s` at `s = (tr U)² + tr U²` with
`d_f Δ_U w + (d_f + 2) w = d_f² w` at `w = ⟨(tr U)² : tr U²⟩` —
all cleared polynomial identities in the residue. -/
set_option maxHeartbeats 4000000

open ground poly genericlift states kernel lap

private def fU : FList := [(0, false)]
private def fAdj : FList := [(0, false), (0, true)]
private def fUU : FList := [(0, false), (0, false)]
private def unitC : Comb := [([1, 0], ([⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]
private def adjC : Comb :=
  [([0, 1], pOne), ([1, 0], ([⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]
private def sC : Comb := [([0, 1], pOne), ([1, 0], pOne)]
private def wC : Comb := [([0, 1], pOne), ([1, 0], negP)]
private def dfp1 : PPair := ([⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩])
private def dfp2 : PPair := ([⟨4, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩])

example : combEqRead fU (lapComb fU 0 [([0], pOne)])
    (scaleComb cfP [([0], pOne)]) := by decide +kernel
example : combEqRead fAdj (lapComb fAdj 0 unitC) [] := by decide +kernel
example : combEqRead fAdj (lapComb fAdj 0 adjC)
    (scaleComb dfP adjC) := by decide +kernel

/-! The action at a variable key off `0`: the adjoint at the key `2`
reads its own Laplacian at `d_f` and the key-`0` Laplacian at the
sum's unit. -/

private def fAdj2 : FList := [(2, false), (2, true)]

example : combEqRead fAdj2 (lapComb fAdj2 2 adjC)
    (scaleComb dfP adjC) := by decide +kernel
example : combEqRead fAdj2 (lapComb fAdj2 0 adjC) [] := by decide +kernel
example : combEqRead fUU
    (scaleComb dfP (lapComb fUU 0 sC) ++ scaleComb (natP 2) sC)
    (scaleComb (pMul dfP dfp1) sC) := by decide +kernel
example : combEqRead fUU
    (scaleComb dfP (lapComb fUU 0 wC) ++ scaleComb dfp2 wC)
    (scaleComb (pMul dfP dfP) wC) := by decide +kernel

/-! The off-eigenvalue refusal: the adjoint at the fundamental's
Casimir refuses. -/

example : ¬ combEqRead fAdj (lapComb fAdj 0 adjC)
    (scaleComb cfP adjC) := by decide +kernel
