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
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground poly genericlift states kernel lap

private def fU : FList := [(false, false)]
private def fAdj : FList := [(false, false), (false, true)]
private def fUU : FList := [(false, false), (false, false)]
private def unitC : Comb := [([1, 0], ([⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]
private def adjC : Comb :=
  [([0, 1], pOne), ([1, 0], ([⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]
private def sC : Comb := [([0, 1], pOne), ([1, 0], pOne)]
private def wC : Comb := [([0, 1], pOne), ([1, 0], negP)]
private def dfp1 : PPair := ([⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩])
private def dfp2 : PPair := ([⟨4, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩])

example : combEqRead fU (lapComb fU false [([0], pOne)])
    (scaleComb cfP [([0], pOne)]) := by decide +kernel
example : combEqRead fAdj (lapComb fAdj false unitC) [] := by decide +kernel
example : combEqRead fAdj (lapComb fAdj false adjC)
    (scaleComb dfP adjC) := by decide +kernel
example : combEqRead fUU
    (scaleComb dfP (lapComb fUU false sC) ++ scaleComb (natP 2) sC)
    (scaleComb (pMul dfP dfp1) sC) := by decide +kernel
example : combEqRead fUU
    (scaleComb dfP (lapComb fUU false wC) ++ scaleComb dfp2 wC)
    (scaleComb (pMul dfP dfP) wC) := by decide +kernel

/-! The off-eigenvalue refusal: the adjoint at the fundamental's
Casimir refuses. -/

example : ¬ combEqRead fAdj (lapComb fAdj false adjC)
    (scaleComb cfP adjC) := by decide +kernel
