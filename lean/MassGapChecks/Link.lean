import MassGap.Link
/-!
The check module for `prop:link`: the batteries re-read the joint
insertion's instances by kernel `decide` at the word index's
combination equality — `Δ_L tr U = c_f tr U`;
`Δ_L χ_adj(U) = d_f χ_adj(U)`; the cross-variable graded reads
`d_f Δ_L s + 2s = d_f (d_f + 1) s` at `s = tr U tr V + tr(UV)`
with `d_f Δ_L w + (d_f + 2) w = d_f² w` at
`w = ⟨tr U tr V : tr(UV)⟩`; and the module energy
`E χ_adj = 4 d_f χ_adj` at the two-plaquette weights
`E = 3 Δ_U + Δ_L + 3 Δ_V`, the `Δ_V` read the sum's unit at the
`V`-free state — all cleared polynomial identities in the
residue. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground poly genericlift states kernel lap link

private def fU : FList := [(false, false)]
private def fAdj : FList := [(false, false), (false, true)]
private def fUV : FList := [(false, false), (true, false)]
private def adjC : Comb :=
  [([0, 1], pOne), ([1, 0], ([⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]
private def sC : Comb := [([0, 1], pOne), ([1, 0], pOne)]
private def wC : Comb := [([0, 1], pOne), ([1, 0], negP)]
private def dfp1 : PPair := ([⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩])
private def dfp2 : PPair := ([⟨4, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩])

example : combEqRead fU (linkComb fU [([0], pOne)])
    (scaleComb cfP [([0], pOne)]) := by decide +kernel
example : combEqRead fAdj (linkComb fAdj adjC)
    (scaleComb dfP adjC) := by decide +kernel
example : combEqRead fUV
    (scaleComb dfP (linkComb fUV sC) ++ scaleComb (natP 2) sC)
    (scaleComb (pMul dfP dfp1) sC) := by decide +kernel
example : combEqRead fUV
    (scaleComb dfP (linkComb fUV wC) ++ scaleComb dfp2 wC)
    (scaleComb (pMul dfP dfP) wC) := by decide +kernel

/-! The module energy at the two-plaquette weights, `Δ_V` reading
the sum's unit at the `V`-free state. -/

example : combEqRead fAdj (lapComb fAdj true adjC) [] := by decide +kernel
example : combEqRead fAdj
    (scaleComb (natP 3) (lapComb fAdj false adjC)
      ++ linkComb fAdj adjC
      ++ scaleComb (natP 3) (lapComb fAdj true adjC))
    (scaleComb (pMul (natP 4) dfP) adjC) := by decide +kernel
