import MassGap.Lattice
/-!
The check module for `con:lattice`: the batteries re-read the
region interface by kernel `decide` at two stated regions — the
one-plaquette square and the theta graph of two squares sharing
one link — the coloring, simplicity and plaquette reads with the
incident lists' values; the plaquette read's one listing per
plaquette at the cyclic reading, refused at the square's boundary
listed twice and listed beside its rotation; the cyclic word's
reads at the square's boundary against its rotations, its
reversal and the theta graph's second boundary; the moved boundary
word at a link map and a reversal family; and the plaquette
permutation read at the square's rotation as stated data, refused
at a link exchange off the region's symmetries and at the data
crossed.
-/

namespace lattice
set_option maxHeartbeats 4000000

open ground

/-! The reads at the two regions. -/

theorem pin1 : wellRead square := by decide +kernel
theorem pin2 : wellRead thetaG := by decide +kernel
theorem pin3 : colorRead square := by decide +kernel
theorem pin4 : simpleRead square := by decide +kernel
theorem pin5 : plaqRead square := by decide +kernel
theorem pin6 : colorRead thetaG := by decide +kernel
theorem pin7 : simpleRead thetaG := by decide +kernel
theorem pin8 : plaqRead thetaG := by decide +kernel

/-! The incident lists: the square's corners at one outgoing and
one incoming link, the theta graph's shared ends at three. -/

theorem pin9 : incident square 0 = [(0, true), (3, false)] := rfl
theorem pin10 : incident square 2 = [(1, false), (2, true)] := rfl
theorem pin11 : (incident thetaG 0).length = 3 := rfl
theorem pin12 : (incident thetaG 3).length = 3 := rfl
theorem pin13 : incident thetaG 4 = [(4, false), (5, true)] := rfl

/-! The plaquette list at one listing per plaquette: the square's
boundary listed twice, and listed beside its rotation, each refuse
the plaquette read, the second at the structural distinctness
holding. -/

private def sqTwice : Region := { square with plaqs := [sqPlaq, sqPlaq] }
private def sqRot : Region :=
  { square with plaqs := [sqPlaq, ground.rotAt 1 sqPlaq] }

theorem pin14 : ¬ plaqRead sqTwice ∧ ¬ ground.distinctList sqTwice.plaqs := by
  decide +kernel
theorem pin15 : ¬ plaqRead sqRot ∧ ground.distinctList sqRot.plaqs := by
  decide +kernel

/-! The cyclic reading: a boundary word against its rotations, its
reversal and a rotation of its reversal, and refused against the
theta graph's second boundary; the moved boundary word at a link
map and a reversal family, the traversal bit flipped at the
reversed source key alone. -/

theorem pin16 : cycEq sqPlaq (ground.rotAt 2 sqPlaq) = true
    ∧ cycEq sqPlaq (revWord sqPlaq) = true
    ∧ cycEq sqPlaq (ground.rotAt 1 (revWord sqPlaq)) = true
    ∧ cycEq sqPlaq (ground.getAt [] thetaG.plaqs 1) = false := by
  decide +kernel
theorem pin17 : moveWord (fun l => l + 1) (fun l => l == 0) [(0, true), (1, false)]
    = [(1, false), (2, false)] := by decide +kernel

/-! The plaquette permutation read at the square's rotation, the
one plaquette fixed with its boundary rotated: the identity the
permutation and its own witness; refused at a link exchange off
the square's symmetries, and at the rotation with the data
crossed. -/

private def sqRotMap : Nat → Nat := fun l => if l == 3 then 0 else l + 1
private def sqSwap01 : Nat → Nat := fun l => if l == 0 then 1 else if l == 1 then 0 else l

theorem pin18 : plaqPermRead square sqRotMap (fun _ => false) (fun q => q) (fun q => q) := by
  decide +kernel
theorem pin19 : ¬ plaqPermRead square sqSwap01 (fun _ => false) (fun q => q) (fun q => q)
    ∧ ¬ plaqPermRead square sqRotMap (fun _ => false) (fun _ => 1) (fun q => q) := by
  decide +kernel

end lattice
