import MassGap.Ground
/-!
`def:excess` — the ruler excess at the residue `r`: the one
polynomial `A(u) = Σ_{j=1}^{r} [1:j] u^j` supported from key one
with the geometric derivative `A' + u^r = 1 + u A'`.  The
coefficients are the scalar pairs `[1:j]` at the keys one through
`r`, the carrier the occupied window's list at the successor
spelling `r = g + 1`; the evaluation at one is the coefficients'
fold; and the derivative display reads coefficientwise as one read
per occupied degree, `j · [1:j] = 1` (`def:poly`'s
successor-weighted shift at these coefficients), `geomRead` the
one-key read and `derivRead` the display over the whole support.
The value read `A(1) = H_r` is `thm:walkresidue`'s, at its own
module.
-/

namespace excess
open ground

/-- The ruler excess's coefficient list: `[1:j]` at the keys one
through `r`, the one polynomial supported from key one, at the
successor spelling `r = g + 1`. -/
def coeffs (g : Nat) : List Pair :=
  (List.range (g + 1)).map (fun i => ⟨Pos.one, posOfSucc i⟩)

/-- The evaluation at one, the coefficients' fold: `A(1)`. -/
def evalOne (g : Nat) : Pair :=
  match coeffs g with
  | [] => Pair.ofPos Pos.one
  | c :: t => t.foldl (fun a b => a + b) c

/-- The geometric-derivative read at a key: `j · [1:j] = 1`, the
display `A' + u^r = 1 + u A'` coefficientwise, `def:poly`'s
successor-weighted shift at the excess's coefficients. -/
def geomRead (j : Pos) : Prop :=
  (Pair.mul (Pair.ofPos j) ⟨Pos.one, j⟩).oneValue (Pair.ofPos Pos.one)

instance (j : Pos) : Decidable (geomRead j) :=
  inferInstanceAs (Decidable (_ = _))

/-- The derivative display over the whole support, one read per
occupied degree. -/
def derivRead (g : Nat) : Prop :=
  ((List.range (g + 1)).all (fun i =>
    if geomRead (posOfSucc i) then true else false)) = true

instance (g : Nat) : Decidable (derivRead g) :=
  inferInstanceAs (Decidable (_ = _))

end excess
