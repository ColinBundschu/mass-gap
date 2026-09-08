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

/-! The joint insertion across a word (`prop:lap`'s clause).  At the
unit word a link's joint insertion against itself is `Δ_W`'s own
display, at the one-letter site and at the adjoint's.  At the
four-link loop's character `χ = tr(U1 U2 U3 U4) tr(...)† − 1`, the
unit at `[1 : d_f]^4` times the four evaluation loops, the joint
insertion of link `3`'s factors against the base link `1`'s across
the arc `U2† U1†` from the base's tail to the link's tail, and across
the other arc `U3 U4`, reads the base's Laplacian joined to the arc's
site at the word's unit, at the evaluation identity; the base's
Laplacian reads `d_f χ` there and refuses `c_f χ`.  At the loop with
link `3` traversed backward, `tr(U1 U2 U3† U4)`, the arc `U3 U2† U1†`
reads the base's Laplacian at the balance partner, the unsigned read
refused. -/

example : combEqRead fU (jointComb fU [] 0 0 [([0], pOne)])
    (lapComb fU 0 [([0], pOne)]) := by decide +kernel
example : combEqRead fAdj (jointComb fAdj [] 0 0 adjC)
    (lapComb fAdj 0 adjC) := by decide +kernel

private def fLoop : FList :=
  [(1, false), (2, false), (3, false), (4, false),
   (4, true), (3, true), (2, true), (1, true)]
private def loopW : List Nat := [3, 0, 1, 2, 7, 4, 5, 6]
private def unitW : List Nat := [7, 6, 5, 4, 3, 2, 1, 0]
private def invDf4 : PPair := pMul invDfP (pMul invDfP (pMul invDfP invDfP))
private def chiC : Comb := [(loopW, pOne), (unitW, pMul negP invDf4)]
private def arcA : FList := [(2, true), (1, true)]
private def arcB : FList := [(3, false), (4, false)]
private def extA : FList := fLoop ++ arcA ++ daggerW arcA
private def extB : FList := fLoop ++ arcB ++ daggerW arcB

example : evalEqRead extA (jointComb fLoop arcA 3 1 chiC)
    (padState fLoop arcA (lapComb fLoop 1 chiC)) := by decide +kernel
example : evalEqRead extB (jointComb fLoop arcB 3 1 chiC)
    (padState fLoop arcB (lapComb fLoop 1 chiC)) := by decide +kernel
example : evalEqRead fLoop (lapComb fLoop 1 chiC) (scaleComb dfP chiC) := by decide +kernel
example : ¬ evalEqRead fLoop (lapComb fLoop 1 chiC) (scaleComb cfP chiC) := by decide +kernel

private def fLoopB : FList :=
  [(1, false), (2, false), (3, true), (4, false),
   (4, true), (3, false), (2, true), (1, true)]
private def arcC : FList := [(3, false), (2, true), (1, true)]
private def extC : FList := fLoopB ++ arcC ++ daggerW arcC
example : evalEqRead extC (jointComb fLoopB arcC 3 1 chiC)
    (padState fLoopB arcC (scaleComb negP (lapComb fLoopB 1 chiC))) := by decide +kernel
example : ¬ evalEqRead extC (jointComb fLoopB arcC 3 1 chiC)
    (padState fLoopB arcC (lapComb fLoopB 1 chiC)) := by decide +kernel

/-! A letter wired to itself withdraws at the joint read: at
`[3, 0, 2, 1]` the two members' fold at the Fierz weight, the
transposition member at the count's power of its loops against the
identity member at the count's cofactor and its loops, reads the
sum's unit at the two-cycle's site. -/

private def selfPair (π : List Nat) : Comb :=
  let t := fierzT π
  let e := fierzI π
  [(t.1, pMul halfP (dfPow t.2)),
   (e.1, pMul halfP (pMul negP (pMul invDfP (dfPow e.2))))]

example : combEqRead fAdj (selfPair [3, 0, 2, 1]) [] := by decide +kernel
example : ¬ combEqRead fAdj (selfPair [3, 0, 1, 2]) [] := by decide +kernel
