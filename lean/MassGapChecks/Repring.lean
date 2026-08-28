import MassGap.Repring
/-!
The check module for `prop:repring`: the batteries re-read the
label index's calculus by kernel `decide` — the unit read and the
orthonormality at a decided window with the general theorems'
routes and the matched width's refusal beside them, the triple
count's rotation at four triples by the general theorem's route
with the two widths' refusals beside them and a transposition, the
associativity fold, and the dimension identity at instances
through the adjoint square (the deferred `lem:blockcount` reads at
their recorded consumer).
-/
set_option maxHeartbeats 4000000

open ground places labels repring

private def labelsUpTo (d k : Nat) : List Shape :=
  (List.range (k + 1)).flatMap (fun j =>
    (allShapes (d - 1) j).map (fun s => s ++ [0]))

/-! The unit read and the orthonormality at one decided window
each, the general theorems the whole windows' own reads. -/

example : ((labelsUpTo 2 2).all (fun a => (labelsUpTo 2 2).all (fun b =>
    if unitRead a b then true else false))) = true := by decide +kernel
example : ((labelsUpTo 2 2).all (fun a => (labelsUpTo 2 2).all (fun b =>
    if orthoRead a b then true else false))) = true := by decide +kernel

/-! The unit read as the general theorem's own route, the
guard-false widths among the instances with the vanished count
beside them. -/

example : unitRead [1, 0] [1, 0] := unitRead_all [1, 0] [1, 0] rfl
example : unitRead [2, 0, 0] [0, 2, 0] :=
  unitRead_all [2, 0, 0] [0, 2, 0] rfl
example : unitRead [1, 1, 0] [1, 1, 0] :=
  unitRead_all [1, 1, 0] [1, 1, 0] rfl
example : unitRead [1, 0, 0] [1, 0, 0] :=
  unitRead_all [1, 0, 0] [1, 0, 0] rfl
example : unitRead ([] : Shape) [] := unitRead_all [] [] rfl

example : countL [1, 0, 0] [1, 0, 0] (unitL 3) = 0 := by decide +kernel
example : ¬ reduce [1, 0, 0] = dualL [1, 0, 0] := by decide +kernel
example : countL [2, 0, 0] [0, 2, 0] (unitL 3) = 1 := by decide +kernel

/-! The matched width's isolating refusal: at a second shape one
letter wider the count reads one while the dual read refuses, the
unit read parting. -/

example : ¬ (([0, 0, 2] : Shape).length = ([0, 0] : Shape).length) := by
  decide +kernel
example : countL [0, 0] [0, 0, 2]
    (unitL ([0, 0] : Shape).length) = 1 := by decide +kernel
example : ¬ (reduce ([0, 0] : Shape) = dualL [0, 0, 2]) := by decide +kernel
example : ¬ unitRead [0, 0] [0, 0, 2] := by decide +kernel

/-! The orthonormality as the general theorem's own route. -/

example : orthoRead [1, 0] [1, 0] := orthoRead_all [1, 0] [1, 0] rfl
example : orthoRead [2, 0, 0] [2, 0, 0] :=
  orthoRead_all [2, 0, 0] [2, 0, 0] rfl
example : orthoRead [1, 1, 0] [0, 1, 1] :=
  orthoRead_all [1, 1, 0] [0, 1, 1] rfl

/-! The triple count's rotation as the general theorem's own route
at four triples, one decided end-to-end beside it, and the
transposition by its own general (the symmetry of `N` at self-dual
labels, the two generators). -/

example : mSymRead [1, 0] [1, 0] [0, 1] := by decide +kernel
example : mSymRead [1, 0] [1, 0] [0, 1] :=
  mSym_all [1, 0] [1, 0] [0, 1] rfl rfl
example : mSymRead [1, 0] [2, 0] [1, 0] :=
  mSym_all [1, 0] [2, 0] [1, 0] rfl rfl
example : mSymRead [1, 0, 0] [1, 0, 0] [0, 1, 0] :=
  mSym_all [1, 0, 0] [1, 0, 0] [0, 1, 0] rfl rfl
example : mSymRead [1, 1, 0] [1, 1, 0] [1, 1, 0] :=
  mSym_all [1, 1, 0] [1, 1, 0] [1, 1, 0] rfl rfl
example : m3 [1, 1, 0] [1, 0, 0] [0, 1, 0]
    = m3 [1, 0, 0] [1, 1, 0] [0, 1, 0] := by decide +kernel
example : m3 [1, 1, 0] [1, 0, 0] [0, 1, 0]
    = m3 [1, 0, 0] [1, 1, 0] [0, 1, 0] :=
  mSym_swap [1, 1, 0] [1, 0, 0] [0, 1, 0] rfl rfl
example : m3 [2, 0] [1, 0] [1, 0] = m3 [1, 0] [2, 0] [1, 0] :=
  mSym_swap [2, 0] [1, 0] [1, 0] rfl rfl

/-! The two matched widths' isolating refusals: at the second
shape one letter wider than the first the two groupings part, and
at the third likewise, the rotation's own binders. -/

example : ¬ mSymRead [0, 0] [0, 0, 2] [0, 0] := by decide +kernel
example : ¬ mSymRead [0, 0] [0, 0] [0, 0, 2] := by decide +kernel

/-! The associativity fold at instances, one decided end-to-end
and the rest by the general theorem's own route. -/

example : assocRead [1, 0] [1, 0] [1, 0] [3, 0] := by decide +kernel
example : assocRead [1, 0] [1, 0] [1, 0] [3, 0] :=
  assocRead_all [1, 0] [1, 0] [1, 0] [3, 0] rfl rfl rfl
example : assocRead [1, 0] [1, 0] [1, 0] [1, 1] :=
  assocRead_all [1, 0] [1, 0] [1, 0] [1, 1] rfl rfl rfl
example : assocRead [1, 0, 0] [1, 0, 0] [1, 0, 0] [1, 1, 0] :=
  assocRead_all [1, 0, 0] [1, 0, 0] [1, 0, 0] [1, 1, 0] rfl rfl rfl
example : assocRead [1, 0, 0] [0, 1, 0] [1, 0, 0] [1, 1, 0] :=
  assocRead_all [1, 0, 0] [0, 1, 0] [1, 0, 0] [1, 1, 0] rfl rfl rfl

/-! The dimension identity at instances, the adjoint square among
them: `lem:blockcount`(ii)'s sum at the tensor product. -/

example : dimRead [1, 0] [1, 0] := by decide +kernel
example : dimRead [2, 0] [2, 0] := by decide +kernel
example : dimRead [1, 0, 0] [1, 0, 0] := by decide +kernel
example : dimRead [1, 0, 0] [1, 1, 0] := by decide +kernel
example : dimRead [1, 1, 0] [1, 1, 0] := by decide +kernel
example : dimRead [1, 0, 0, 0] [1, 0, 0, 0] := by decide +kernel
