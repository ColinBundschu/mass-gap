import MassGap.Places
import MassGap.Genericlift
/-!
`con:states` — the permutation presentation's states.  A factor is
a variable with its dagger read, one of the four letters
(`Factor`, the pair of the variable's and the dagger's reads), and
a factor list fixes the presentation's site (`FList`).  A generator
`Φ_π` is indexed by a wiring at the places — `π(i) = j` records
that the row index of factor `i` is contracted against the column
index of factor `j` — the wiring total with every place's value
once (`permAt`); its trace structure is the wiring's cycles
(`places.cyclesOf`, `con:places`' orbit words).  States are the generators' combinations at
polynomial-pair coefficients in the residue (`Comb` at
`lem:genericlift`'s pairs), the trace-polynomial reduction of the
walled Brauer category: the group enters only as the loop value
`d_f` of the calculus, `prop:wg`'s pairing the reads' own
carrier and `rem:kernel`'s word index the combinations' gauge-free
key.  The presentation's product concatenates the sites and blocks
the wirings — the first's wiring against the second's shifted by
the first's site length (`mulComb` at `shiftW`), the coefficients
at the pairs' product — and a state's coefficient at a wiring is
the literal key's fold over the combination (`coeffAtW`, the
generator basis's read).  An action's linear extension over a state
is the per-generator images at the coefficients' products
(`extComb`, the insertion reads' shared carrier).
-/

namespace states
open ground places

/-- A factor: the variable's read with the dagger's, one of the
four letters. -/
abbrev Factor := Bool × Bool

/-- A factor list, the presentation's site. -/
abbrev FList := List Factor

/-- A wiring at the places: the assignment total with every place's
value once. -/
def permAt (π : List Nat) (m : Nat) : Prop :=
  π.length = m
  ∧ ((List.range m).all (fun j => ground.countOf j π == 1)) = true

instance (π : List Nat) (m : Nat) : Decidable (permAt π m) :=
  inferInstanceAs (Decidable (_ ∧ _ = _))

/-- A state: a formal combination of the generators at
polynomial-pair coefficients in the residue, keyed by the
wirings. -/
abbrev Comb := List (List Nat × poly.PPair)

/-- The wiring shifted by an offset, the concatenated site's second
block. -/
def shiftW (n : Nat) (π : List Nat) : List Nat :=
  π.map (fun j => j + n)

/-- The presentation's product: the sites concatenate and the wirings
block, the first's wiring against the second's shifted, the
coefficients at the pairs' product. -/
def mulComb (a b : Comb) : Comb :=
  a.flatMap (fun ea => b.map (fun eb =>
    (ea.1 ++ shiftW ea.1.length eb.1,
     poly.pMul ea.2 eb.2)))

/-- A state's coefficient at a wiring, the literal key's fold — the
generator basis's read (`rem:kernel`'s word coefficient is the class
sum). -/
def coeffAtW (c : Comb) (π : List Nat) : poly.PPair :=
  c.foldl (fun acc e =>
    if e.1 == π then poly.pAdd acc e.2 else acc)
    poly.pZero

/-- An action's linear extension over a state, the per-generator
images at the coefficients' products. -/
def extComb (act : List Nat → Comb) (c : Comb) : Comb :=
  c.flatMap (fun e => (act e.1).map (fun t =>
    (t.1, poly.pMul e.2 t.2)))

/-- A state's key list, one wiring joined per refusal. -/
def suppOf (c : Comb) : List (List Nat) :=
  c.foldl (fun acc e =>
    if acc.any (fun v => v == e.1) then acc else acc ++ [e.1]) []

/-- A state collected at its key list: one entry per occupied
wiring, the key's fold at its reduced representative — the
combination the occupancy family over the wirings (`rem:kernel`'s
projection at the generator keys), every fold over the state
reading the collected form at the key folds' own values, the
representative `lem:genericlift`'s certified reduction. -/
def collect (c : Comb) : Comb :=
  (suppOf c).map (fun w => (w, genericlift.pReduce (coeffAtW c w)))

end states
