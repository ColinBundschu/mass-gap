import MassGap.Wg
/-!
`rem:kernel` — the word index, and the presentation kernel.  The
states are indexed gauge-free by the multisets of oriented cyclic
words in the four letters: a generator reads only its cycles'
words, each up to rotation, so the positions of repeated factors
are a gauge mode of the wiring spelling — the word of a cycle is
its factors' letter list at the least rotation (`fCode` the
letters' keys, `canonRot`), and the index is the canonical words'
sorted multiset (`wordsOf` at the lexicographic insertion `sortW`);
two wirings at one word multiset are one state (`oneState`), and a
state's word coefficient is the class sum of its wiring
coefficients (`coeffAt`), so identities of character polynomials
close on the word index outright, coefficient comparisons per word
multiset before any pairing (`combEqRead` at the polynomial pairs'
cross reads).  The word index's one further datum is the kernel:
the evaluation identity `Σ_j U_ij Ū_kj = δ_ik` imposes
per-residue relations among the generators within a factor list,
the null space of the pairing's Gram, one finite projection at
every residue (`kernelRead`: the keys total and pairwise off one
state, the residue beyond the clearance radius — the factor
count's own comparison, `prop:wg`'s stated boundary, the
symbolic checker's domain — the vector at the pairs' site reads
occupied at the residue, and every Gram row's fold a value at the
residue reading equal members there, the row's site read the
defensive conjunct beside the radius); a residue at or below the
radius reads the direct tag at the residue's own carrier, the
at-residue Gram through the label calculus (`prop:wg`'s
derivation): a single-variable cycle word reduces at the
evaluation identity to its net power — a net-zero cycle the
residue's count, a scalar — and a state's variable datum is its
winding pair, per variable the net powers' undaggered side against
the daggered side's, read at every wiring whose cycles each sit at
one variable (`windingOf`); the character read `χ^λ(μ)` is the
alternant extraction at the residue's count (`charAt`,
`p_μ a_u = Σ_λ χ^λ(μ) a_{λ+u}` at `pmuCoeff`'s monomial
coefficient, the within-residue shapes `partsAt` at
`places.allShapes`' row lists); two generators pair at the residue
at the character fold, per variable the `χ`-reads folded over the
shared shapes of the two winding sides with the net-zero cycles'
count multiplied through (`pairAt`, the conjugation `wg.pairPhi`'s
own); and a combination is the presentation kernel's member at the
residue exactly where its pairing reads the sum's unit against
every wiring of the list, the at-residue Gram's own row read
(`directRead`: the factor list's factors at one variable, the
coefficients occupied at the residue — the occupancy conjunct the
symbolic checker's own beside the rows — and `rowFold`'s
cross-added coefficient fold at `pairAt` per generator; the
generators span the carrier, so rows at the unit close the
membership at the pairing's definiteness).
Determinant relations are invisible at the symbolic residue — the
calculus computes the generic theory, `r = 1` its own window read
while `r ≥ 2` reads generically — and the produced null spaces are
the emitted gate's records per factor list, the read here their
checker.  The member's own symbolic read sits beside it: a state
pairing to equal members against every generator at the site
(`nullRead`, the relations the ones holding at every residue), and
the tag branch joins the two at the radius comparison (`memberAt`:
a factor count below the residue reads the symbolic member, at or
above it the direct), `con:res`'s member sentence the recorded
consumer. -/

namespace kernel
open ground poly places states genericlift

/-- The letters' keys, the four factors encoded. -/
def fCode (f : states.Factor) : Nat :=
  (if f.1 then 2 else 0) + (if f.2 then 1 else 0)

private def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: s, b :: t =>
    if a < b then true else if b < a then false else lexLe s t

/-- The canonical rotation, the least of a cyclic word's
readings. -/
def canonRot (w : List Nat) : List Nat :=
  (List.range w.length).foldl (fun best k =>
    let rot := ground.rotAt k w
    if lexLe rot best then rot else best) w

private def insertW (w : List Nat) : List (List Nat) → List (List Nat)
  | [] => [w]
  | v :: t => if lexLe w v then w :: v :: t else v :: insertW w t

private def sortW (ws : List (List Nat)) : List (List Nat) :=
  ws.foldl (fun acc w => insertW w acc) []

/-- The gauge-free index: the wiring's cyclic words at the factor
list, each at its canonical rotation, the multiset sorted. -/
def wordsOf (F : states.FList) (π : List Nat) : List (List Nat) :=
  sortW ((places.cyclesOf π).map (fun c =>
    canonRot (c.map (fun i =>
      fCode (ground.getAt (false, false) F i)))))

/-- Two wirings at one word multiset are one state, the repeated
factors' positions the gauge mode. -/
def oneState (F : states.FList) (a b : List Nat) : Prop :=
  wordsOf F a = wordsOf F b

instance (F : states.FList) (a b : List Nat) :
    Decidable (oneState F a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- A state's word coefficient, the class sum of its wiring
coefficients at the key. -/
def coeffAt (F : states.FList) (c : states.Comb)
    (w : List (List Nat)) : poly.PPair :=
  c.foldl (fun acc e =>
    if wordsOf F e.1 == w then poly.pAdd acc e.2 else acc)
    poly.pZero

/-- A state's site read: every coefficient at the pair's occupied
second member, `def:ground`'s positive datum mirrored. -/
def combOcc (c : states.Comb) : Prop :=
  (c.all (fun e => decide (genericlift.pairOcc e.2))) = true

instance (c : states.Comb) : Decidable (combOcc c) :=
  inferInstanceAs (Decidable (_ = _))

/-- Two states read one value exactly at every word coefficient:
identities close on the word index outright, before any pairing,
the coefficients at the pairs' site reads. -/
def combEqRead (F : states.FList) (a b : states.Comb) : Prop :=
  combOcc a ∧ combOcc b
  ∧ ((a ++ b).all (fun e => decide (genericlift.crossNull
      (coeffAt F a (wordsOf F e.1))
      (coeffAt F b (wordsOf F e.1))))) = true

instance (F : states.FList) (a b : states.Comb) :
    Decidable (combEqRead F a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ = _))

/-- The presentation kernel's read at a residue: the wiring keys
total and pairwise off one state, a stated vector at the pairs'
site reads occupied at the residue — some coefficient's value off
the sum's unit there, every second member's value occupied there —
whose every Gram-row fold reads equal members at the residue, the
pairing the Gram's own read.  The row fold accumulates at the
certified reduction (`lem:genericlift`'s `pAddR`, the moved
representative one value with its own pair); `coeffAt` and
`states.coeffAtW` fold the displayed `pAdd` at their few duplicate
keys. -/
def kernelRead (F : states.FList) (keys : List (List Nat))
    (ks : List poly.PPair) (rv : BPair) : Prop :=
  keys.length = ks.length
  ∧ (keys.all (fun k => decide (states.permAt k F.length))) = true
  ∧ ((List.range keys.length).all (fun i =>
      (List.range i).all (fun j =>
        !(decide (oneState F (ground.getAt [] keys i)
          (ground.getAt [] keys j)))))) = true
  ∧ BPair.ofNat F.length < rv
  ∧ (ks.all (fun c =>
      decide (genericlift.pairOccAt c rv))) = true
  ∧ ¬ (ks.all (fun c =>
      decide ((poly.eval c.1 rv).oneValue BPair.unit))) = true
  ∧ ((List.range keys.length).all (fun i =>
      let row := (List.range keys.length).foldl (fun acc j =>
        genericlift.pAddR acc (poly.pMul
          (ground.getAt poly.pZero ks j)
          (wg.pairPhi F F (ground.getAt [] keys i)
            (ground.getAt [] keys j)))) poly.pZero
      decide (genericlift.pairOccAt row rv)
        && decide (genericlift.agreeAt row poly.pZero rv)))
    = true

instance (F : states.FList) (keys : List (List Nat))
    (ks : List poly.PPair) (rv : BPair) :
    Decidable (kernelRead F keys ks rv) :=
  inferInstanceAs
    (Decidable (_ ∧ _ ∧ _ = _ ∧ _ < _ ∧ _ = _ ∧ ¬ _ = _ ∧ _ = _))

/-- A presentation-kernel member's read, symbolic: the state's
pairing against every generator at the site reads equal members —
the evaluation identity's relations, the ones holding at every
residue (`kernelRead` is the at-residue record's checker). -/
def nullRead (F : states.FList) (k : states.Comb) : Prop :=
  ((places.perms F.length).all (fun π => decide (genericlift.crossNull
    (wg.pairFull F F [(π, poly.pOne)] k)
    poly.pZero))) = true

instance (F : states.FList) (k : states.Comb) :
    Decidable (nullRead F k) :=
  inferInstanceAs (Decidable (_ = _))

/-! The direct tag: the at-residue Gram through the label
calculus.  A single-variable cycle word reduces at the evaluation
identity to its net power, the character read extracts over the
alternants at the residue's count, and the member read is the
at-residue Gram's row read, the pairing against every wiring of
the list at the sum's unit. -/

/-- The power product's monomial coefficient: `pmuCoeff μ e` reads
`[x^e] p_μ` at `p_μ = Π_i p_{μ_i}`, `p_m = Σ_j x_j^m` — the vacant
part list reads the unit exactly at the all-zero exponent, and a
part folds over the positions carrying at least it, the exponent
lowered there. -/
def pmuCoeff : List Nat → List Nat → Nat
  | [], e => if (e.all (fun a => a == 0)) then 1 else 0
  | m :: rest, e =>
    (List.range e.length).foldl (fun acc j =>
      if m ≤ ground.getAt 0 e j then
        acc + pmuCoeff rest (ground.editAt (fun x => x - m) j e)
      else acc) 0

/-- The character read `χ^λ(μ)`, the alternant extraction at the
residue's count: `p_μ a_u = Σ_λ χ^λ(μ) a_{λ+u}` at `u_j = rv-1-j`,
the coefficient at the display `λ+u` summed over the place
permutations at the swap grading, each subtraction behind its
comparison; a shape beyond the residue's rows reads the sum's
unit. -/
def charAt (rv : Nat) (lam mu : List Nat) : BPair :=
  if rv < lam.length then BPair.unit
  else
    (BPair.sum ((places.perms rv).map (fun w =>
      if ((List.range rv).all (fun j =>
          rv - ground.getAt 0 w j
            ≤ ground.getAt 0 lam j + (rv - j))) then
        let rest := (List.range rv).map (fun j =>
          ground.getAt 0 lam j + (rv - j)
            - (rv - ground.getAt 0 w j))
        let v := BPair.ofNat (pmuCoeff mu rest)
        if places.parity w then v.swap else v
      else BPair.unit))).norm

/-- The shapes of a stated box total at rows within the residue:
`places.allShapes`' enumeration at the row-list display. -/
def partsAt (k rv : Nat) : List (List Nat) :=
  (places.allShapes rv k).map places.rowList

/-- A state's variable datum, the winding pair per variable: over
the wiring's cycles, each cycle's members read off the factor
list — a cycle across the two variables refuses the read whole —
and a single-variable cycle reduces at the evaluation identity to
its net power, the undaggered margin joining the first list, the
daggered the second, a cycle at equal counts the counter's scalar;
the value is the `U`-variable's triple with the `V`-variable's. -/
def windingOf (F : states.FList) (π : List Nat) :
    Option ((List Nat × List Nat × Nat)
      × (List Nat × List Nat × Nat)) :=
  (places.cyclesOf π).foldl (fun acc c =>
    match acc, c with
    | none, _ => none
    | some t, [] => some t
    | some (tU, tV), i :: rest =>
      let v := (ground.getAt (false, false) F i).1
      if ((i :: rest).all (fun j =>
          (ground.getAt (false, false) F j).1 == v)) then
        let u := ((i :: rest).filter (fun j =>
          !(ground.getAt (false, false) F j).2)).length
        let d := (i :: rest).length - u
        let t := if v then tV else tU
        let t' :=
          if d < u then (t.1 ++ [u - d], t.2.1, t.2.2)
          else if u < d then (t.1, t.2.1 ++ [d - u], t.2.2)
          else (t.1, t.2.1, t.2.2 + 1)
        some (if v then (tU, t') else (t', tV))
      else none)
    (some (([], [], 0), ([], [], 0)))

/-- A variable's read at the residue: at matched winding totals
the character fold over the shared within-residue shapes, at
unmatched totals the sum's unit, the net-zero cycles' count a
residue factor either way. -/
private def varFold (rv : Nat) (t : List Nat × List Nat × Nat) :
    BPair :=
  (if ground.sumNat t.1 = ground.sumNat t.2.1 then
    BPair.sum ((partsAt (ground.sumNat t.1) rv).map (fun l =>
      charAt rv l t.1 * charAt rv l t.2.1))
  else BPair.unit)
  * BPair.ofNat (Nat.pow rv t.2.2)

/-- The at-residue pairing of two generators, `prop:wg`'s direct
tag: the conjugated first key against the second at the
concatenated site exactly as `wg.pairPhi` wires it, the product's
winding data read per variable and the two variables' character
folds multiplied; a wiring crossing the variables refuses the
read, the crossing class the factor list's own Gram's
(`rem:kernel`'s computation). -/
def pairAt (F : states.FList) (pa pb : List Nat) (rv : Nat) :
    Option BPair :=
  match windingOf (wg.conjF F ++ F)
      (places.invPerm F.length pa ++ states.shiftW F.length pb) with
  | none => none
  | some (tU, tV) => some ((varFold rv tU * varFold rv tV).norm)

/-- The row fold at a generator: the combination's coefficients
evaluate at the residue through the Horner reads and enter at
their `pairAt` pairings against the generator, the fold the
`(num, den)` cross addition at the reduced representatives, the
value the numerator's — the occupancy conjunct beside the read
keeps the second members off the unit at the residue. -/
private def rowFold (F : states.FList) (c : states.Comb) (rv : Nat)
    (g : List Nat) : BPair :=
  (c.foldl (fun acc e =>
    let n := (poly.eval e.2.1 (BPair.ofNat rv)
      * ((pairAt F g e.1 rv).getD BPair.unit)).norm
    let d := (poly.eval e.2.2 (BPair.ofNat rv)).norm
    ground.cpAdd acc (n, d))
    (BPair.unit, BPair.ofNat 1)).1

/-- The direct member read at the residue, the at-residue Gram's
own row read (`prop:wg`'s direct member sentence): the factor
list's factors at one variable, every coefficient occupied at the
residue, and the combination's pairing against every wiring of
the list reading the sum's unit — the generators span the
carrier, so rows at that unit close the membership at the
pairing's definiteness, and a member's rows are the null
function's own. -/
def directRead (F : states.FList) (c : states.Comb) (rv : Nat) :
    Prop :=
  ((F.all (fun f => !f.1) || F.all (fun f => f.1))
    && c.all (fun e =>
        if genericlift.pairOccAt e.2 (BPair.ofNat rv) then true
        else false)
    && (places.perms F.length).all (fun g =>
        if (rowFold F c rv g).oneValue BPair.unit then true
        else false)) = true

instance (F : states.FList) (c : states.Comb) (rv : Nat) :
    Decidable (directRead F c rv) :=
  inferInstanceAs (Decidable (_ = _))

/-- The member read's tag branch, `con:res`'s member sentence: a
factor count below the residue — the residue beyond the clearance
radius, `kernelRead`'s own comparison — reads the symbolic member,
and a residue at or below the radius reads the direct member at
the residue's own carrier. -/
def memberAt (F : states.FList) (c : states.Comb) (rv : Nat) :
    Prop :=
  if F.length < rv then nullRead F c else directRead F c rv

instance (F : states.FList) (c : states.Comb) (rv : Nat) :
    Decidable (memberAt F c rv) :=
  inferInstanceAs (Decidable
    (if F.length < rv then nullRead F c else directRead F c rv))

end kernel
