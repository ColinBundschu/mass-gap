import MassGap.Repring
/-!
The check module for `prop:repring`: the batteries re-read the
label index's calculus by kernel `decide` — the unit read and the
orthonormality at a decided window with the general theorems'
routes and the matched width's refusal beside them, the triple
count's rotation at four triples by the general theorem's route
with the two widths' refusals beside them and a transposition, the
associativity fold, and the dimension identity at instances
through the adjoint square, with the dimension theorem at every
matched-width pair and its width refusal.
-/

namespace repring
set_option maxHeartbeats 4000000

open ground places labels

private def labelsUpTo (d k : Nat) : List Shape :=
  (List.range (k + 1)).flatMap (fun j =>
    (allShapes (d - 1) j).map (fun s => s ++ [0]))

/-! The unit read and the orthonormality at one decided window
each, the general theorems the whole windows' own reads. -/

theorem pin1 : ((labelsUpTo 2 2).all (fun a => (labelsUpTo 2 2).all (fun b =>
    if unitRead a b then true else false))) = true := by decide +kernel
theorem pin2 : ((labelsUpTo 2 2).all (fun a => (labelsUpTo 2 2).all (fun b =>
    if orthoRead a b then true else false))) = true := by decide +kernel

/-! The unit read as the general theorem's own route, the
guard-false widths among the instances with the vanished count
beside them. -/

theorem pin3 : unitRead [1, 0] [1, 0] := unitRead_all [1, 0] [1, 0] rfl
theorem pin4 : unitRead [2, 0, 0] [0, 2, 0] :=
  unitRead_all [2, 0, 0] [0, 2, 0] rfl
theorem pin5 : unitRead [1, 1, 0] [1, 1, 0] :=
  unitRead_all [1, 1, 0] [1, 1, 0] rfl
theorem pin6 : unitRead [1, 0, 0] [1, 0, 0] :=
  unitRead_all [1, 0, 0] [1, 0, 0] rfl
theorem pin7 : unitRead ([] : Shape) [] := unitRead_all [] [] rfl

theorem pin8 : countL [1, 0, 0] [1, 0, 0] (unitL 3) = 0 := by decide +kernel
theorem pin9 : ¬ reduce [1, 0, 0] = dualL [1, 0, 0] := by decide +kernel
theorem pin10 : countL [2, 0, 0] [0, 2, 0] (unitL 3) = 1 := by decide +kernel

/-! The matched width's isolating refusal: at a second shape one
letter wider the count reads one while the dual read refuses, the
unit read parting. -/

theorem pin11 : ¬ (([0, 0, 2] : Shape).length = ([0, 0] : Shape).length) := by
  decide +kernel
theorem pin12 : countL [0, 0] [0, 0, 2]
    (unitL ([0, 0] : Shape).length) = 1 := by decide +kernel
theorem pin13 : ¬ (reduce ([0, 0] : Shape) = dualL [0, 0, 2]) := by decide +kernel
theorem pin14 : ¬ unitRead [0, 0] [0, 0, 2] := by decide +kernel

/-! The orthonormality as the general theorem's own route. -/

theorem pin15 : orthoRead [1, 0] [1, 0] := orthoRead_all [1, 0] [1, 0] rfl
theorem pin16 : orthoRead [2, 0, 0] [2, 0, 0] :=
  orthoRead_all [2, 0, 0] [2, 0, 0] rfl
theorem pin17 : orthoRead [1, 1, 0] [0, 1, 1] :=
  orthoRead_all [1, 1, 0] [0, 1, 1] rfl

/-! The triple count's rotation as the general theorem's own route
at four triples, one decided end-to-end beside it, and the
transposition by its own general (the symmetry of `N` at self-dual
labels, the two generators). -/

theorem pin18 : mSymRead [1, 0] [1, 0] [0, 1] := by decide +kernel
theorem pin19 : mSymRead [1, 0] [1, 0] [0, 1] :=
  mSym_all [1, 0] [1, 0] [0, 1] rfl rfl
theorem pin20 : mSymRead [1, 0] [2, 0] [1, 0] :=
  mSym_all [1, 0] [2, 0] [1, 0] rfl rfl
theorem pin21 : mSymRead [1, 0, 0] [1, 0, 0] [0, 1, 0] :=
  mSym_all [1, 0, 0] [1, 0, 0] [0, 1, 0] rfl rfl
theorem pin22 : mSymRead [1, 1, 0] [1, 1, 0] [1, 1, 0] :=
  mSym_all [1, 1, 0] [1, 1, 0] [1, 1, 0] rfl rfl
theorem pin23 : m3 [1, 1, 0] [1, 0, 0] [0, 1, 0]
    = m3 [1, 0, 0] [1, 1, 0] [0, 1, 0] := by decide +kernel
theorem pin24 : m3 [1, 1, 0] [1, 0, 0] [0, 1, 0]
    = m3 [1, 0, 0] [1, 1, 0] [0, 1, 0] :=
  mSym_swap [1, 1, 0] [1, 0, 0] [0, 1, 0] rfl rfl
theorem pin25 : m3 [2, 0] [1, 0] [1, 0] = m3 [1, 0] [2, 0] [1, 0] :=
  mSym_swap [2, 0] [1, 0] [1, 0] rfl rfl

/-! The two matched widths' isolating refusals: at the second
shape one letter wider than the first the two groupings part, and
at the third likewise, the rotation's own binders. -/

theorem pin26 : ¬ mSymRead [0, 0] [0, 0, 2] [0, 0] := by decide +kernel
theorem pin27 : ¬ mSymRead [0, 0] [0, 0] [0, 0, 2] := by decide +kernel

/-! The associativity fold at instances, one decided end-to-end
and the rest by the general theorem's own route. -/

theorem pin28 : assocRead [1, 0] [1, 0] [1, 0] [3, 0] := by decide +kernel
theorem pin29 : assocRead [1, 0] [1, 0] [1, 0] [3, 0] :=
  assocRead_all [1, 0] [1, 0] [1, 0] [3, 0] rfl rfl rfl
theorem pin30 : assocRead [1, 0] [1, 0] [1, 0] [1, 1] :=
  assocRead_all [1, 0] [1, 0] [1, 0] [1, 1] rfl rfl rfl
theorem pin31 : assocRead [1, 0, 0] [1, 0, 0] [1, 0, 0] [1, 1, 0] :=
  assocRead_all [1, 0, 0] [1, 0, 0] [1, 0, 0] [1, 1, 0] rfl rfl rfl
theorem pin32 : assocRead [1, 0, 0] [0, 1, 0] [1, 0, 0] [1, 1, 0] :=
  assocRead_all [1, 0, 0] [0, 1, 0] [1, 0, 0] [1, 1, 0] rfl rfl rfl

/-! The dimension identity at instances, the adjoint square among
them: `lem:blockcount`(ii)'s sum at the tensor product. -/

theorem pin33 : dimRead [1, 0] [1, 0] := by decide +kernel
theorem pin34 : dimRead [2, 0] [2, 0] := by decide +kernel
theorem pin35 : dimRead [1, 0, 0] [1, 0, 0] := by decide +kernel
theorem pin36 : dimRead [1, 0, 0] [1, 1, 0] := by decide +kernel
theorem pin37 : dimRead [1, 1, 0] [1, 1, 0] := by decide +kernel
theorem pin38 : dimRead [1, 0, 0, 0] [1, 0, 0, 0] := by decide +kernel

/-! The dimension theorem at matched widths, including full-column
representatives and the unit list. The mismatched width refuses the
identity: its shape enumeration is vacant at positive degree. -/

theorem pin39 : dimRead [1, 0] [1, 0] := dimRead_all [1, 0] [1, 0] rfl
theorem pin40 : dimRead [1, 1, 0] [1, 1, 0] :=
  dimRead_all [1, 1, 0] [1, 1, 0] rfl
theorem pin41 : dimRead [1, 0, 0, 0] [1, 0, 0, 0] :=
  dimRead_all [1, 0, 0, 0] [1, 0, 0, 0] rfl
theorem pin42 : dimRead [1, 1] [0, 1] := dimRead_all [1, 1] [0, 1] rfl
theorem pin43 : dimRead [1, 1] [0, 1] := by decide +kernel
theorem pin44 : dimRead [] [] := dimRead_all [] [] rfl
theorem pin45 : ¬ dimRead [] [1, 0] := by decide +kernel

end repring
