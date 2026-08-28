import MassGap.Twoplaq
/-!
The check module for `con:twoplaq`: the batteries re-read the
two-plaquette data by kernel `decide` at hand-derived instances.
The sites first — the extension at a variable's pair and the word
fold's order, the leftmost letter extending first — with the level
`4 d_f` at its own value.  The module presentation at the bare pair
reads the adjoint's presentation at the coefficients, `[1 : 1]` at
the open wiring and `-[1 : d_f]` at the closed, and refuses the
literal list identity: `modPres`' closed coefficient is the same
value at a different representative, so state identities pin at the
values and never at the lists.  With one contraction the reads
carry it: at `[U, U†, V, V†]` the pairing `(2, 3)` sends the base
wiring to `[0, 1, 3, 2]` at `[1 : d_f]` and the open pair's exchange
to `[1, 0, 3, 2]` at `-[1 : d_f]²`.  `modPresOk` reads that stated
data: both presentations pass, and the five refusals are a place
list colliding at `(1, 0)`, the daggers entered out of order, a
place past the site's top, an uncovering pair at the four-letter
site (the other factors' places untouched — the reviewer's own
probe class), and the chosen pair crossing variables at a covering
list
at the four-letter list.

The electric action's eigen-read next, both components: at the site
`[U, U†]` the `V`-Laplacian reads the sum's unit and the two
surviving weights collect to `2 c_f + [1 : d_f] = d_f` at the open
wiring with `-1` at the closed, so `E` reads `4 d_f` at the open
key and `-4` at the closed, against `4 d_f` times the presentation's
own `[1 : 1]` and `-[1 : d_f]` — the module level `lvlE`'s two
components, `prop:lap`'s and `prop:link`'s displays collected.

The resolvent step then: `|tr U|²` deflates off the module at the
cofactor `-1`, so the deflated side reads the sum's unit at the
open key and `[1 : d_f]` at the closed — the unit presentation —
and the support `[[0, 1], [1, 0]]` closes under the insertion while
`[[0, 1]]` alone refuses (the mixed contraction leaves the closed
key).  `E` annihilates the unit presentation at both keys, its own
read here, so the level alone carries the solve and the solution is
that presentation at `-[1 : 4 d_f]`; `stepRead` reads the four steps
whole at that data.  Its refusals: the degenerate module whose
self-pairing is the sum's unit, and the solve at the undeflated
scale, which reads `-4` where the deflated side reads `[1 : d_f]`.

Last the magnetic multiplication's coefficient at one plaquette
word.  The same-plaquette read is the cubic count
`⟨Φ_q1, χ_U Φ_q1⟩ = Eval(χ_adj³) = N^adj_{adj,adj} = 2`,
`prop:repring`'s display at the adjoint triple; the cross-plaquette
read is the sum's unit, the second module state's variable never
meeting the multiplied first's — `Eval(χ_V) Eval(χ_U²)` with the
`V` factor alone vanishing.

The cubic count is the module's one read over the single-pin
budget, the budget exception's reason.  `stepRead`
carries two deflation certificates, the withdrawn state's and the
solution's, and their coefficients hold the pairing's cofactor at
`lem:genericlift`'s certified reduction, so `pairFull` against the
deflated side meets the true `[1 : d_f]` rather than the evaluation
denominators multiplied through, `con:res`' seam at this
module's doubled certificate.  The cubic count's cost is the
evaluation's: the pairing's concatenated site carries three `U`
factors against three daggered, so every generator folds the
six-permutation Weingarten solve — the three-box tier, the
factorial route's recorded cost, and the ceiling on any battery
here (nothing beyond three pairs per variable), the reduction at
the bilinear fold's seam carried and the Weingarten solve the
floor beneath. -/
set_option maxHeartbeats 4000000

open ground poly genericlift states kernel lap res fiber twoplaq

/-- The four-factor site, one pair per variable. -/
private def f4 : FList :=
  [(false, false), (false, true), (true, false), (true, true)]

/-- The unit presentation's coefficient, `[1 : d_f]`. -/
private def uC : PPair := ([⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩])

/-- The squared trace's presentation, `|tr U|²`. -/
private def sqC : Comb := [([0, 1], pOne)]

/-- The unit's presentation, `[1 : d_f] tr(U U†)`. -/
private def unitC : Comb := [([1, 0], ([⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]

/-- The solve's solution: the unit presentation at the level's own
withdrawn scale, `-[1 : 4 d_f]`. -/
private def xC : Comb := scaleComb (pMul negP (pCofactor pOne lvlE)) unitC

/-- The step's support, the insertion's closed key list. -/
private def wsE : List (List Nat) := [[0, 1], [1, 0]]

/-! The sites and the level: the extension at a variable's pair, the
word fold's order, and `4 d_f` at its own value. -/

example : extSite true siteQ1 = f4 := by decide +kernel
example : wordSite [false]
    = [(false, false), (false, true), (false, false), (false, true)] := by
  decide +kernel
example : wordSite [false, true]
    = [(false, false), (false, true), (false, false), (false, true),
       (true, false), (true, true)] := by decide +kernel
example : crossNull lvlE ([⟨5, 1⟩, ⟨5, 1⟩], [⟨2, 1⟩]) := by decide +kernel

/-! The module presentation at the bare pair: the adjoint's
presentation at the values, the literal list identity refused at
the representative gauge — the closed coefficient is
`pMul (-[1 : d_f]) [1 : 1]`, one value at a different pair of
polynomials. -/

example : crossNull (coeffAtW (modPres siteQ1 0 1 []) [0, 1]) pOne := by
  decide +kernel
example : crossNull (coeffAtW (modPres siteQ1 0 1 []) [1, 0])
    ([⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]) := by decide +kernel
example : ¬ (modPres siteQ1 0 1 [] = phiAdj) := by decide +kernel

/-! The presentation with one contraction at `[U, U†, V, V†]`: the
pairing `(2, 3)`'s base wiring at `[1 : d_f]`, the open pair's
exchange at `-[1 : d_f]²`. -/

example : crossNull (coeffAtW (modPres f4 0 1 [(2, 3)]) [0, 1, 3, 2]) uC := by
  decide +kernel
example : crossNull (coeffAtW (modPres f4 0 1 [(2, 3)]) [1, 0, 3, 2])
    ([⟨1, 2⟩], [⟨2, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩]) := by decide +kernel

/-! The presentation's stated data read for itself: the bare pair
and the one-contraction site pass, and the four refusals — a place
list colliding at `(1, 0)`, the daggers entered out of order, a
place past the site's top, and the chosen pair crossing variables
at the four-letter list. -/

example : modPresOk siteQ1 0 1 [] := by decide +kernel
example : modPresOk f4 0 1 [(2, 3)] := by decide +kernel
example : ¬ modPresOk siteQ1 0 1 [(1, 0)] := by decide +kernel
example : ¬ modPresOk siteQ1 1 0 [] := by decide +kernel
example : ¬ modPresOk siteQ1 0 3 [] := by decide +kernel
example : ¬ modPresOk f4 0 1 [] := by decide +kernel
example : ¬ modPresOk
    [(false, false), (true, true), (true, false), (true, true)]
    0 1 [(2, 3)] := by decide +kernel

/-! The electric action's eigen-read at the module level, both
components: `E Φ_q1 = 4 d_f Φ_q1` at the open and the closed key. -/

example : crossNull (pAdd (coeffAtW (extComb (eAct siteQ1) phiAdj) [0, 1])
    (pMul negP (pMul lvlE (coeffAtW phiAdj [0, 1])))) pZero := by decide +kernel
example : crossNull (pAdd (coeffAtW (extComb (eAct siteQ1) phiAdj) [1, 0])
    (pMul negP (pMul lvlE (coeffAtW phiAdj [1, 0])))) pZero := by decide +kernel

/-! The resolvent step at the graph's own datum: the deflated
side's coefficients, the insertion's kernel point at the unit
presentation, the support's closure, and the four steps whole. -/

example : crossNull (coeffAtW (deflate siteQ1 [phiAdj] sqC) [0, 1]) pZero := by
  decide +kernel
example : crossNull (coeffAtW (deflate siteQ1 [phiAdj] sqC) [1, 0]) uC := by
  decide +kernel
example : crossNull (coeffAtW (extComb (eAct siteQ1) unitC) [0, 1]) pZero := by
  decide +kernel
example : crossNull (coeffAtW (extComb (eAct siteQ1) unitC) [1, 0]) pZero := by
  decide +kernel
example : closedE (eAct siteQ1) wsE := by decide +kernel
example : ¬ closedE (eAct siteQ1) [[0, 1]] := by decide +kernel

/-! The step's whole certificate at the two deflation
certificates' reduced cofactors — `con:res`' shape doubled by
step 4, the reduction carrying both. -/

example : stepRead siteQ1 [phiAdj] wsE sqC xC [] := by decide +kernel

/-! The step's refusals: the degenerate module at the sum's unit
self-pairing, and the solve at the undeflated scale. -/

example : ¬ stepRead siteQ1 [([] : Comb)] wsE sqC xC [] := by decide +kernel
example : ¬ solveRead (eAct siteQ1) lvlE wsE unitC [] unitC := by decide +kernel

/-! The magnetic multiplication's coefficient at one plaquette word:
the same-plaquette cubic count `Eval(χ_adj³) = N^adj_{adj,adj} = 2`
at the three-box tier's six-permutation Weingarten solve per
generator — the module's heaviest read — and the cross-plaquette
sum's unit beside it. -/

example : crossNull (pairP siteQ1 (wordSite [false]) phiAdj (mulAdj phiAdj))
    ([⟨3, 1⟩], [⟨2, 1⟩]) := by decide +kernel

example : crossNull (coeffP (wordSite [false]) (mulAdj phiAdj)) pZero := by
  decide +kernel
