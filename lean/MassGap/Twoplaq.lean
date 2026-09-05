import MassGap.Res
import MassGap.Fiber
import MassGap.Link
/-!
`con:twoplaq` — the two-plaquette data on `con:fiber`'s carrier.
The graph fixes the electric weights outright: four links per
plaquette with one shared, so three unshared each and the shared
one counted once, `E = 3 Δ_U + Δ_L + 3 Δ_V` at the displayed
`(3, 1, 3)` (`eAct`, `prop:lap`'s and `prop:link`'s actions summed
at the site).  The section's operators sit at the trace form, where
`C_2(adj) = d_f`, so the energies read weight-free — the
conversion's own — and the module level is `4 d_f` (`lvlE`).  The
module states `Φ_q1`, `Φ_q2` are one presentation, the adjoint
character's `phiAdj`, read at the two sites `siteQ1`, `siteQ2`: the
SITE carries the variable and the wiring list is site-blind, so the
`U` and the `V` module differ by their factor lists alone.  The
magnetic multiplications read per plaquette — `χ_X(W)` extends the
factor list at the variable's pair and multiplies the presentation
there (`extSite`, `mulAdj` at `con:states`' product), a `k`-step
image one state per plaquette word (`wordSite`, the extensions'
fold from the first module state's site) — and the displayed
coefficient is the pairing identity's fold over the words, `coeffP`
the one word's read, the second module state against the multiplied
one at `con:fiber`'s `pairP`, the fold its consumers' own over
their stated sites, the same-plaquette read `Eval(χ_U³)` the
cubic count `N^adj_{adj,adj}` and the cross-plaquette read the sum's
unit.  The module presentations at a site are the adjoint's pair at
the chosen factors with the paired `[1 : d_f]`-contractions at the
rest, the open and closed wirings at their coefficients (`modPres`).
Its stated data reads for itself (`modPresOk`, the store checker's
conjunct at its arrival): the touched places the site's own
wiring — the pair with the contractions covering the other
factors, each place once, `states.permAt`'s read — the chosen
factors one variable's undaggered and daggered letters, and every
contraction pair one variable's own matched letters; a collided
OR an uncovering presentation is a well-formed list denoting the
wrong object, and that silent-toxic misuse is the class the guard
names.
One solve per resolvent step lands at the `(E : 4 d_f)` site datum
(`stepRead` at `res.resRead`, this graph's instantiation of
`con:res` and the consumer read closing the resolvent seam), the
batteries at hand-derived instances.
-/

namespace twoplaq
open ground poly places states genericlift

/-- The first module state's site, the `U` pair. -/
def siteQ1 : states.FList := [(0, false), (0, true)]

/-- The second module state's site, the `V` pair. -/
def siteQ2 : states.FList := [(1, false), (1, true)]

/-- The adjoint character's presentation at a variable pair: the
open wiring at the unit with the closed at the withdrawn
`[1 : d_f]`, `lem:adjchar`'s display at the two-letter site. -/
def phiAdj : states.Comb :=
  [([0, 1], poly.pOne),
   ([1, 0], ([⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]

/-- The electric action at a site, the displayed weights:
`E = 3 Δ_U + Δ_L + 3 Δ_V`, forced by the graph — four links per
plaquette, one shared, three unshared each. -/
def eAct (F : states.FList) (π : List Nat) : states.Comb :=
  lap.scaleComb (lap.natP 3) (lap.lapAct F 0 π)
  ++ link.linkAct F π
  ++ lap.scaleComb (lap.natP 3) (lap.lapAct F 1 π)

/-- The module level at the trace form, `4 d_f`. -/
def lvlE : poly.PPair :=
  poly.pMul (lap.natP 4) lap.dfP

/-- The site extended at a variable's pair, the magnetic
multiplication's list. -/
def extSite (W : Nat) (F : states.FList) : states.FList :=
  F ++ [(W, false), (W, true)]

/-- One magnetic multiplication, per plaquette: the state against
the adjoint's presentation at the extended site's pair. -/
def mulAdj (c : states.Comb) : states.Comb :=
  states.mulComb c phiAdj

/-- A plaquette word's site, the extensions' fold from the first
module state's. -/
def wordSite (w : List Nat) : states.FList :=
  w.foldl (fun F W => extSite W F) siteQ1

/-- A module presentation at a site: the adjoint's pair at the
chosen factors with the paired `[1 : d_f]`-contractions at the
rest, the open and closed wirings at their coefficients —
`con:res` step 1's parenthetical at `lem:adjchar`'s
presentation. -/
def modPres (F : states.FList) (i j : Nat)
    (rest : List (Nat × Nat)) : states.Comb :=
  let paired := rest.foldl (fun w p => lap.swapIdx p.1 p.2 w)
    (List.range F.length)
  let cPow := rest.foldl (fun c _ => poly.pMul c
    ([⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩])) poly.pOne
  [(paired, cPow),
   (lap.swapIdx i j paired,
    poly.pMul ([⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]) cPow)]

/-- A module presentation's validity read: the touched places the
site's own wiring — the chosen pair with the contractions covering
the other factors, each place once (`states.permAt`'s read) — the
chosen factors one variable's undaggered and daggered letters, and
every contraction pair one variable's own matched letters —
`modPres`'s stated-data guard, the store checker's conjunct at its
arrival. -/
def modPresOk (F : states.FList) (i j : Nat)
    (rest : List (Nat × Nat)) : Prop :=
  states.permAt (i :: j :: rest.flatMap (fun p => [p.1, p.2]))
    F.length
  ∧ (((ground.getAt (0, false) F i).2 == false)
   && ((ground.getAt (0, false) F j).2 == true)
   && ((ground.getAt (0, false) F i).1
      == (ground.getAt (0, false) F j).1)
   && (rest.all (fun p =>
      ((ground.getAt (0, false) F p.1).2 == false)
      && ((ground.getAt (0, false) F p.2).2 == true)
      && ((ground.getAt (0, false) F p.1).1
         == (ground.getAt (0, false) F p.2).1)))) = true

instance (F : states.FList) (i j : Nat) (rest : List (Nat × Nat)) :
    Decidable (modPresOk F i j rest) :=
  inferInstanceAs (Decidable (_ ∧ _ = _))

/-- One resolvent step's certificate at a word's site: the
multiplied state at the extended list, the solve at the pair
`(E : 4 d_f)`'s site datum there — `con:res`'s reads at this
graph's instantiation. -/
def stepRead (F : states.FList) (mods : List states.Comb)
    (ws : List (List Nat)) (y x k : states.Comb) : Prop :=
  res.resRead F (eAct F) lvlE mods ws y x k

instance (F : states.FList) (mods : List states.Comb)
    (ws : List (List Nat)) (y x k : states.Comb) :
    Decidable (stepRead F mods ws y x k) :=
  inferInstanceAs (Decidable (res.resRead _ _ _ _ _ _ _ _))

/-- The displayed coefficient's read at a step: the second module
state's pairing against the multiplied solution, the pairing
identity's value at the two stated lists. -/
def coeffP (Fx : states.FList) (x : states.Comb) : poly.PPair :=
  fiber.pairP siteQ2 Fx phiAdj x

end twoplaq
