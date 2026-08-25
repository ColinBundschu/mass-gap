import MassGap.Res
/-!
The check module for `con:res`: the batteries re-read the
resolvent's four steps by kernel `decide` at the adjoint site's
hand-derived instances.  Step 1 deflates `|tr U|²` off `χ_adj` at
the cofactor `-⟨χ_adj, |tr U|²⟩ / ⟨χ_adj, χ_adj⟩ = -1`, so the
`[0, 1]` mass cancels and the `[1, 0]` mass reads `[1 : d_f]` —
the unit presentation, `deflateRead` its certificate.  Step 2
closes the `U`-insertion's support in one round off `[[0, 1]]`,
the unclosed list refusing (the mixed contraction leaves `[0, 1]`
for `[1, 0]`), and the reads are ordering-free — only the keys'
membership is consumed.  Step 3 reads the `U`-Laplacian's kernel
point at `prop:lap`'s pin `1 = [1 : d_f] tr(U U†)`: the insertion
collects to the sum's unit at the support key, so at the level one
the solution is `-1` against the unit's right side.  Step 4's
member read holds at the sum's unit and refuses at `|tr U|²`, whose
pairing against the identity generator is occupied.  Beside them
the matrix route's data: the site datum square at the two-key basis
and the cofactor `c_f / d_f = [t(t + 2) : 2(t + 1)²]` at the pair
carrier, with the off-order shape refusal.

Step 1's certificate is the module's heaviest read: the deflated
side's
coefficients carry the pairing's cofactor at `lem:genericlift`'s
certified reduction, so the `pairFull` fold against it meets the
true `[1 : d_f]` at two keys where the unreduced cofactor stood at
thirty-one, and `crossNull` closes on that degree.  The seam is the
coefficient's own — the same read at the bare coefficients (the two
`coeffAtW` batteries above) decides beside it, and the whole
certificate sits inside the half-second budget's own order. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground poly genericlift states kernel lap res

private def fAdj : FList := [(false, false), (false, true)]

/-- The squared trace's presentation, `|tr U|²`. -/
private def sqC : Comb := [([0, 1], pOne)]

/-- The unit's presentation, `[1 : d_f] tr(U U†)`. -/
private def unitC : Comb := [([1, 0], ([⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]

/-- The adjoint character's presentation,
`|tr U|² - [1 : d_f] tr(U U†)`. -/
private def adjC : Comb :=
  [([0, 1], pOne), ([1, 0], ([⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]

/-- The unit presentation's coefficient, `[1 : d_f]`. -/
private def uC : PPair := ([⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩])

/-- The `U`-insertion at the adjoint site, the stated action. -/
private def actU : List Nat → Comb := fun π => lapAct fAdj false π

/-! Step 1, the deflated side. -/

example : crossNull (coeffAtW (deflate fAdj [adjC] sqC) [0, 1]) pZero := by
  decide +kernel
example : crossNull (coeffAtW (deflate fAdj [adjC] sqC) [1, 0]) uC := by
  decide +kernel
example : deflateRead fAdj [adjC] sqC := by decide +kernel

/-! Step 2, the support's closure. -/

example : closedE actU (closeE actU 2 (suppOf sqC)) := by decide +kernel
example : ¬ closedE actU [[0, 1]] := by decide +kernel
example : ¬ covers [] sqC := by decide +kernel

/-! Step 3, the solve at the kernel point. -/

example : solveRead actU pOne (closeE actU 2 (suppOf unitC))
    (scaleComb negP unitC) [] unitC := by decide +kernel

/-! Step 4, the kernel member's read. -/

example : nullRead fAdj ([] : Comb) := by decide +kernel
example : ¬ nullRead fAdj sqC := by decide +kernel

/-! The matrix route's data at the pair carrier. -/

example : ppSquare 2 (siteMat actU pOne [[0, 1], [1, 0]]) := by decide +kernel
example : ¬ ppSquare 2 [[pOne]] := by decide +kernel
example : ppadjRead (siteMat actU pOne [[0, 1], [1, 0]]) := by decide +kernel
example : crossNull (pCofactor cfP dfP)
    ([BPair.unit, ⟨3, 1⟩, ⟨2, 1⟩], [⟨3, 1⟩, ⟨5, 1⟩, ⟨3, 1⟩]) := by decide +kernel
