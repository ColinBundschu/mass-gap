import MassGap.Lattice
/-!
The check module for `con:lattice`: the batteries re-read the
region interface by kernel `decide` at two stated regions — the
one-plaquette square and the theta graph of two squares sharing
one link — the coloring, simplicity and plaquette reads with the
incident lists' values.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground lattice

/-! The reads at the two regions. -/

example : wellRead square := by decide +kernel
example : wellRead thetaG := by decide +kernel
example : colorRead square := by decide +kernel
example : simpleRead square := by decide +kernel
example : plaqRead square := by decide +kernel
example : colorRead thetaG := by decide +kernel
example : simpleRead thetaG := by decide +kernel
example : plaqRead thetaG := by decide +kernel

/-! The incident lists: the square's corners at one outgoing and
one incoming link, the theta graph's shared ends at three. -/

example : incident square 0 = [(0, true), (3, false)] := rfl
example : incident square 2 = [(1, false), (2, true)] := rfl
example : (incident thetaG 0).length = 3 := rfl
example : (incident thetaG 3).length = 3 := rfl
example : incident thetaG 4 = [(4, false), (5, true)] := rfl
