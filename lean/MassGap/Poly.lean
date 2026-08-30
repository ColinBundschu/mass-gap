import MassGap.Ground
/-!
`def:poly` — a polynomial over the balance pairs is the recursion
`P = c + z Q`, a constant read with a shifted family, finitely deep;
equivalently its occupancy family of coefficients at the variable's
monomials, here the total coefficient list at the monomial keys, the
recursion the list's own cons.  The tex's ground-pair reading lands
with its consumer, `thm:windowsep`'s descent: a scalar datum enters
this calculus cleared of its second member, the homogeneity
principle's rescaling (a comparison holds exactly at its
rescaling).  The sum adds componentwise over the monomial
keys, the product convolves — on the recursion,
`(c + z P) Q = c Q + z (P Q)`, the shifted term's constant the
sum's unit, and the product's own unit the single scalar-one
coefficient (`one`, the carrier's spelling of the constant
polynomial the convolution reads off, `one_mul`) — and the
evaluation is the Horner read on the recursion,
additive and multiplicative at the one-value read (`eval_add`,
`eval_mul`).  A composite point `[ln : c]` reads through the
cleared evaluation `Σ_k p_k ln^k c^(K-k)` (`evalClear`), whose
integer representative is the variable's clearing at the entries
`p_k c^(K-k)` (`clearVar`): the cleared list's Horner read is that
evaluation (`eval_clearVar`), its derivative is the derivative's
clearing one power down (`deriv_clearVar`), and a value's
representative clears to its own representative
(`vnorm_clearVar`).  The clearing passes the displayed reads: the
sum componentwise at the one stated power (`clearVar_add`), the
memberwise swap entrywise (`clearVar_neg`), and the convolution at
the joined power, each factor within its stated power
(`clearVar_mul`), and the cleared evaluation reads them at the
value: a sum's summands (`evalClear_add`), the memberwise swap's
balance partner (`evalClear_neg`), a product's factors at the split
powers (`evalClear_mul`), a rescaling at the scale's multiple
(`evalClear_scaleP`) and a higher stated power at the shared
positive power's weight (`evalClear_pow`).  The division at a
monic `S` is the descent from the top, the monic top clearing each
summit, the pair `(Q, R)` at the
naming identity `P = S Q + R` with `R`'s keys below `S`'s top; a
monic divisor enters as its below-top coefficient list, the top the
scalar one by the shape.  That pair is one value at every solution
(`div_unique`): two representations with remainders below the top
differ by a quotient whose monic-scaled top term sits above every
remainder key, so the quotients agree and the remainders with them;
the cancellation beneath it is its own read, a monic multiple
reading a polynomial within the divisor's below-top length forces
the cofactor to the unit tail (`monic_cancel`).  A factor list
folds at the product's unit (`prodFold`) and every stated member
divides the fold at a cofactor inside it (`prodFold_factor`).
The naming identity is the stated decidable read `divRead`, its
identity instances the check module's, and the derivative's
Leibniz rule is the theorem `deriv_mul`, the convolution identity
at every key pair; the remainder lists at a monic `S` sum
componentwise with the product the convolution's remainder at the
division by `S`.  A polynomial's top is its largest key's
coefficient (`top`, the carrier-general `topO` at its last-member
read `topO_getAt`), the product's top is the tops' product
(`top_mul`) with the carrier at occupied factors one key below the
tops' join (`length_mul`), whence the integral read: a product at
the sum's unit puts one factor's every coefficient there
(`unitTail_mul_of`, `of_unitTail_mul`) with the shared-factor
withdrawal beside it — a shared factor of occupied top withdraws at
two products of one value (`pmul_cancel`) — a factor fold reading the
unit at a value exactly where a listed factor does (`prodFold_unit`,
`prodFoldMap_unit`) and a rescaled list evaluating to the rescaled
value (`eval_mapScale`); the multiplicity at a monic
factor is the count of iterated exact divisions (`multAt`), read at
its factorization with the uniqueness (`multAt_read`, `multAt_of`),
additive over a product (`multAt_mul`), positive exactly at a root
(`multAt_pos`), a repeated root a root of the derivative
(`multAt_deriv`), and a class read (`multAt_congr`, `multAt_powOf`).
A root is a value at which the linear factor's remainder — the
Horner read — has its two members equal
(`isRoot`), the roots of a product its factors' own
(`isRoot_mul`), of a positive power its base's (`isRoot_powOf`),
and the monic linear factor reads the sum's unit at its own root
(`eval_monic_linear`).

The carrier's own algebra closes the module: the sum commutes and
associates, the product distributes over either factor's sum, a
scale transports across it, and the product commutes and
associates — the convolution read as the balance pairs' algebra one
monomial key at a time, with `add_neg` the memberwise swap's
cancellation and `one_mul` the unit monomial's read.  A
coefficient family against a polynomial family is `scaleDot`, each
coefficient's rescaling of its own polynomial summed key by key,
the walk stopping at whichever family runs out — `def:split`'s
congruence and `lem:fiberdec`'s row action its two consumers.  The deck
families' doubling identity (`def:deck`; `lem:fiberdec`) is the
kit's consumer.  The monomial kit closes the module at `def:poly`'s
words: the monomial `mono` with its signed spelling `smono`, the
geometric word `gword` and the pair `tpair` at its monic display
and its split off the word, the product's bilinearity over the sum
fold (`mul_famFold`), the monic cancellation with its power
corollary (`mul_cancel_monic`, `powOf_cancel_monic`), and the
signed-monomial fold read back at its per-key coefficient counts
(`monoFold_getAt`, `monoFold_ov`) — `cor:weyldim`'s member half the
consumer.
-/

namespace poly
open ground

/-- A polynomial over the balance pairs: the total coefficient list
over the monomial keys below the stated top. -/
abbrev Poly := List BPair

/-! `def:poly`'s displayed reads at a general entry carrier: the
recursion's sum and convolution at any operations bundle
(`ground.DOps`), one spelling per operation, each concrete
carrier's operations its instance — the balance pairs at
`ground.bpairOps`, the balance-pair polynomials at `polyOps`, and
the iterated carrier at `polyO polyOps`. -/

/-- The sum adds componentwise over the monomial keys, the longer
list's tail riding, at a stated entry bundle. -/
def addLO {γ : Type} (ops : DOps γ) : List γ → List γ → List γ
  | [], q => q
  | c :: p, [] => c :: p
  | c :: p, d :: q => ops.add c d :: addLO ops p q

/-- The sum at a vacant second summand reads the first list. -/
theorem addNilO {γ : Type} (ops : DOps γ) :
    ∀ p : List γ, addLO ops p [] = p
  | [] => rfl
  | _ :: _ => rfl

/-- The product convolves, each coefficient one fold over the key
pairs at its monomial: on the recursion,
`(c + z P) Q = c Q + z (P Q)`, at a stated entry bundle. -/
def mulLO {γ : Type} (ops : DOps γ) : List γ → List γ → List γ
  | [], _ => []
  | c :: p, q =>
    addLO ops (q.map (ops.mul c)) (ops.unit :: mulLO ops p q)

/-- The polynomial carrier's own bundle over an entry bundle: the
sum and the convolution with the vacant list the sum's unit, the
product's unit the entry one's singleton, and the balance partner
entrywise. -/
def polyO {γ : Type} (ops : DOps γ) : DOps (List γ) :=
  { add := addLO ops, mul := mulLO ops, unit := [],
    one := [ops.one], swap := fun p => p.map ops.swap }

/-- The sum adds componentwise over the monomial keys, the longer
list's tail riding — the recursion at the balance-pair entries. -/
def add : Poly → Poly → Poly := addLO bpairOps

theorem add_nil : ∀ p : Poly, add p [] = p := addNilO bpairOps

/-- The product convolves, each coefficient one fold over the key
pairs at its monomial — the convolution at the balance-pair
entries. -/
def mul : Poly → Poly → Poly := mulLO bpairOps

/-- The balance-pair polynomials' own entry bundle, the functor at
the balance pairs. -/
def polyOps : DOps Poly := polyO bpairOps

/-- The product's unit at the polynomial carrier. -/
def one : Poly := [BPair.ofPos .one]

/-- The power at a stated count at any entry carrier, the product's
fold from the one. -/
def powO {γ : Type} (ops : DOps γ) (x : γ) : Nat → γ
  | 0 => ops.one
  | n + 1 => ops.mul x (powO ops x n)

/-- The power at a stated count, the product's fold from the
unit. -/
def powOf (p : Poly) : Nat → Poly := powO polyOps p

/-- The natural weight at a stated count at any entry carrier, the
sum's fold from its unit, one summand per count. -/
def nsmulO {γ : Type} (ops : DOps γ) (x : γ) : Nat → γ
  | 0 => ops.unit
  | n + 1 => ops.add x (nsmulO ops x n)

/-- The evaluation is the Horner read on the recursion. -/
def eval : Poly → BPair → BPair
  | [], _ => BPair.unit
  | c :: p, r => c + r * eval p r

/-- The successor-weighted shift from a stated key. -/
def derivFrom : Pos → Poly → Poly
  | _, [] => []
  | n, c :: p => c.scale n :: derivFrom (succ n) p

/-- The derivative `P'_h = (h+1) P_{h+1}` at every key. -/
def deriv : Poly → Poly
  | [] => []
  | _ :: p => derivFrom .one p

/-! `def:poly`'s one-value read at a general entry read: the one
recursion over the coefficient lists at any read bundle
(`ground.DRead`), a key beyond one list's top read against the
sum's unit — each concrete carrier's read its instance, the
balance-pair polynomials at `ground.bpairRead` and the iterated
carrier at `listRead`, each level's read the construction at the
level below's own. -/

/-- A tail beyond the shorter top reads one value against the sum's
unit at every key, at a stated entry read. -/
def unitTailO {γ : Type} (ops : DOps γ) (R : DRead γ) :
    List γ → Prop
  | [] => True
  | c :: p => R.rel c ops.unit ∧ unitTailO ops R p

/-- Two coefficient lists read one value where every key's
coefficients do, a key beyond one list's top read against the
sum's unit, at a stated entry read. -/
def listOV {γ : Type} (ops : DOps γ) (R : DRead γ) :
    List γ → List γ → Prop
  | [], q => unitTailO ops R q
  | c :: p, [] => R.rel c ops.unit ∧ unitTailO ops R p
  | c :: p, d :: q => R.rel c d ∧ listOV ops R p q

/-- The tail read's decision, the entry read's fold. -/
def decUnitTailO {γ : Type} (ops : DOps γ) (R : DRead γ) :
    ∀ p : List γ, Decidable (unitTailO ops R p)
  | [] => isTrue trivial
  | _ :: p => @instDecidableAnd _ _ (R.dec _ _) (decUnitTailO ops R p)

instance {γ : Type} (ops : DOps γ) (R : DRead γ) (p : List γ) :
    Decidable (unitTailO ops R p) := decUnitTailO ops R p

/-- The one-value read's decision, the entry read's fold. -/
def decListOV {γ : Type} (ops : DOps γ) (R : DRead γ) :
    ∀ p q : List γ, Decidable (listOV ops R p q)
  | [], q => decUnitTailO ops R q
  | _ :: p, [] =>
    @instDecidableAnd _ _ (R.dec _ _) (decUnitTailO ops R p)
  | _ :: p, _ :: q =>
    @instDecidableAnd _ _ (R.dec _ _) (decListOV ops R p q)

instance {γ : Type} (ops : DOps γ) (R : DRead γ) (p q : List γ) :
    Decidable (listOV ops R p q) := decListOV ops R p q

/-- The list carrier's own read bundle over an entry read, the
level's one-value read at the level below's own. -/
def listRead {γ : Type} (ops : DOps γ) (R : DRead γ) :
    DRead (List γ) :=
  ⟨listOV ops R, decListOV ops R⟩

/-- A tail beyond the shorter top reads one value against the sum's
unit at every key. -/
def unitTail : Poly → Prop := unitTailO bpairOps bpairRead

/-- Two polynomials read one value where every key's coefficients
do, a key beyond one list's top read against the sum's unit. -/
def oneValue : Poly → Poly → Prop := listOV bpairOps bpairRead

/-- The tail read's decision at the balance-pair entries. -/
def decUnitTail (p : Poly) : Decidable (unitTail p) :=
  decUnitTailO bpairOps bpairRead p

instance (p : Poly) : Decidable (unitTail p) := decUnitTail p

/-- The one-value read's decision at the balance-pair entries. -/
def decOneValue (p q : Poly) : Decidable (oneValue p q) :=
  decListOV bpairOps bpairRead p q

instance (p q : Poly) : Decidable (oneValue p q) := decOneValue p q

/-! The division at a monic `S`, the descent from the top. -/

private def padTo (n : Nat) (l : List BPair) : List BPair :=
  List.replicate (n - l.length) BPair.unit ++ l

private def subTop : List BPair → List BPair → List BPair
  | rest, [] => rest
  | [], _ :: _ => []
  | r :: rest, d :: ds => (r + d.swap) :: subTop rest ds

private def divGo : Nat → List BPair → List BPair →
    List BPair × List BPair
  | 0, stf, ptf => ([], padTo stf.length ptf)
  | fuel + 1, stf, ptf =>
    if ptf.length ≤ stf.length then ([], padTo stf.length ptf)
    else
      match ptf with
      | [] => ([], padTo stf.length [])
      | c :: rest =>
        let s := divGo fuel stf (subTop rest (stf.map (fun d => c * d)))
        (c :: s.1, s.2)

/-- The monic polynomial from its below-top coefficient list, the
top the scalar one by the shape. -/
def monic (s : Poly) : Poly := s ++ [BPair.ofPos .one]

/-- The list at its stated positive top, the certificate reads'
divisor spelling (`thm:windowsep`, the divisor at its primitive
list with the stated positive top). -/
def topped (g : Poly) (t : Pos) : Poly := g ++ [BPair.ofPos t]

/-- The division at a monic `S`, entered as its below-top list: the
pair `(Q, R)`, quotient and remainder, `R` total below `S`'s top. -/
def div (s P : Poly) : Poly × Poly :=
  let g := divGo P.length s.reverse P.reverse
  (g.1.reverse, g.2.reverse)

/-- The naming identity `P = S Q + R` at the division's output, one
value at every key, the descent's read. -/
def divRead (s P : Poly) : Prop :=
  oneValue (add (mul (monic s) (div s P).1) (div s P).2) P

instance (s P : Poly) : Decidable (divRead s P) := decOneValue _ _

/-- The remainder lists at a monic `S`: sums componentwise, the
product the convolution's remainder at the division by `S`. -/
def remMul (s a b : Poly) : Poly := (div s (mul a b)).2

/-! The Horner read's coherence with the componentwise sum and the
convolution. -/

/-- A one-coefficient list's Horner read is its coefficient. -/
theorem eval_one (c r : BPair) : (eval [c] r).oneValue c :=
  BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl c) (BPair.mul_unit r))
    (BPair.add_unit c)

/-- The evaluation is additive over the componentwise sum. -/
theorem eval_add : ∀ (p q : Poly) (r : BPair),
    (eval (add p q) r).oneValue (eval p r + eval q r)
  | [], q, r => BPair.oneValue_symm (BPair.unit_add (eval q r))
  | c :: p, [], r => BPair.oneValue_symm (BPair.add_unit (eval (c :: p) r))
  | c :: p, d :: q, r => by
    show ((c + d) + r * eval (add p q) r).oneValue
      ((c + r * eval p r) + (d + r * eval q r))
    have h1 : ((c + d) + r * eval (add p q) r).oneValue
        ((c + d) + r * (eval p r + eval q r)) :=
      BPair.add_congr (BPair.oneValue_refl _)
        (BPair.mul_congr (BPair.oneValue_refl r) (eval_add p q r))
    have e : (c + d) + r * (eval p r + eval q r)
        = (c + r * eval p r) + (d + r * eval q r) := by
      rw [BPair.left_distrib, BPair.add_add_comm]
    exact e ▸ h1

/-- The evaluation reads a scaled list at the scale's product. -/
theorem eval_scale : ∀ (q : Poly) (c r : BPair),
    (eval (q.map (fun d => c * d)) r).oneValue (c * eval q r)
  | [], c, _ => BPair.oneValue_symm (BPair.mul_unit c)
  | d :: q, c, r => by
    show (c * d + r * eval (q.map (fun d => c * d)) r).oneValue
      (c * (d + r * eval q r))
    have h1 : (c * d + r * eval (q.map (fun d => c * d)) r).oneValue
        (c * d + r * (c * eval q r)) :=
      BPair.add_congr (BPair.oneValue_refl _)
        (BPair.mul_congr (BPair.oneValue_refl r) (eval_scale q c r))
    have e : c * d + r * (c * eval q r) = c * (d + r * eval q r) := by
      rw [BPair.mul_left_comm r c (eval q r), ← BPair.left_distrib]
    exact e ▸ h1

/-- The evaluation is multiplicative over the convolution: the
product convolves and the Horner read agrees. -/
theorem eval_mul : ∀ (p q : Poly) (r : BPair),
    (eval (mul p q) r).oneValue (eval p r * eval q r)
  | [], q, r => BPair.oneValue_symm (BPair.unit_mul (eval q r))
  | c :: p, q, r => by
    show (eval (add (q.map (fun d => c * d))
      (BPair.unit :: mul p q)) r).oneValue
      ((c + r * eval p r) * eval q r)
    have h1 := eval_add (q.map (fun d => c * d))
      (BPair.unit :: mul p q) r
    have h2 : (eval (q.map (fun d => c * d)) r
        + eval (BPair.unit :: mul p q) r).oneValue
        (c * eval q r + (BPair.unit + r * (eval p r * eval q r))) :=
      BPair.add_congr (eval_scale q c r)
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.mul_congr (BPair.oneValue_refl r) (eval_mul p q r)))
    have h3 : (c * eval q r
        + (BPair.unit + r * (eval p r * eval q r))).oneValue
        (c * eval q r + r * (eval p r * eval q r)) :=
      BPair.add_congr (BPair.oneValue_refl _)
        (BPair.unit_add (r * (eval p r * eval q r)))
    have e : c * eval q r + r * (eval p r * eval q r)
        = (c + r * eval p r) * eval q r := by
      rw [← BPair.mul_assoc r (eval p r) (eval q r),
        ← BPair.right_distrib]
    exact BPair.oneValue_trans h1 (BPair.oneValue_trans h2 (e ▸ h3))

/-! The evaluation's read: a balance pair against a stated gap of
counts, the Horner step carrying the coefficient and the
argument's scale, and the accumulating passes that carry a read to
their end. -/

/-- A pair's one-value read at a stated gap of counts. -/
def reads (p : BPair) (u v : Nat) : Prop :=
  p.oneValue ⟨posOfSucc u, posOfSucc v⟩

instance (p : BPair) (u v : Nat) : Decidable (reads p u v) :=
  inferInstanceAs (Decidable (_ = _))

/-- The sum's unit reads the vacant gap. -/
theorem reads_unit : reads BPair.unit 0 0 := rfl

/-- A count's entry at its one-member site. -/
private theorem ofNat_pair : ∀ d : Nat,
    BPair.ofNat d = ⟨posOfSucc d, posOfSucc 0⟩
  | 0 => rfl
  | _ + 1 => rfl

/-- The Horner step's own gap at concrete members. -/
private theorem stepId (x y d u v : Nat) :
    ((⟨posOfSucc x, posOfSucc y⟩ : BPair)
        + ⟨posOfSucc d, posOfSucc 0⟩
          * ⟨posOfSucc u, posOfSucc v⟩).oneValue
      ⟨posOfSucc (x + d * u), posOfSucc (y + d * v)⟩ := by
  show ({ pred := x + (d * u + d + u + (0 * v + 0 + v) + 1) + 1
            + (y + d * v) + 1 } : Pos)
    = { pred := x + d * u
          + (y + (d * v + d + v + (0 * u + 0 + u) + 1) + 1) + 1 }
  refine congrArg Pos.mk ?_
  rw [
    Nat.zero_mul v,
    Nat.zero_add 0,
    Nat.zero_add v,
    Nat.zero_mul u,
    Nat.zero_add 0,
    Nat.zero_add u]
  conv => lhs; rw [
    ← Nat.add_assoc x (d * u + d + u + v) 1,
    ← Nat.add_assoc x (d * u + d + u) v,
    ← Nat.add_assoc x (d * u + d) u,
    ← Nat.add_assoc x (d * u) d,
    ← Nat.add_assoc (x + d * u + d + u + v + 1 + 1) y (d * v)]
  conv => rhs; rw [
    ← Nat.add_assoc (x + d * u) (y + (d * v + d + v + u + 1)) 1,
    ← Nat.add_assoc (x + d * u) y (d * v + d + v + u + 1),
    ← Nat.add_assoc (x + d * u + y) (d * v + d + v + u) 1,
    ← Nat.add_assoc (x + d * u + y) (d * v + d + v) u,
    ← Nat.add_assoc (x + d * u + y) (d * v + d) v,
    ← Nat.add_assoc (x + d * u + y) (d * v) d,
    Nat.add_right_comm (x + d * u + y) (d * v) d,
    Nat.add_right_comm (x + d * u) y d,
    Nat.add_right_comm (x + d * u + d + y + d * v) v u,
    Nat.add_right_comm (x + d * u + d + y) (d * v) u,
    Nat.add_right_comm (x + d * u + d) y u,
    Nat.add_right_comm (x + d * u + d + u + y) (d * v) v,
    Nat.add_right_comm (x + d * u + d + u) y v,
    Nat.add_right_comm (x + d * u + d + u + v + y) (d * v) 1,
    Nat.add_right_comm (x + d * u + d + u + v) y 1,
    Nat.add_right_comm (x + d * u + d + u + v + 1 + y) (d * v) 1,
    Nat.add_right_comm (x + d * u + d + u + v + 1) y 1]

/-- The Horner step: the coefficient's gap joins the argument's
scale of the read below. -/
theorem reads_step {p : BPair} {u v : Nat}
    (h : reads p u v) (x y d : Nat) :
    reads (⟨posOfSucc x, posOfSucc y⟩ + BPair.ofNat d * p)
      (x + d * u) (y + d * v) := by
  rw [
    ofNat_pair d]
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.mul_congr (BPair.oneValue_refl _) h))
    (stepId x y d u v)

/-- A read at a gap that clears to a count reads that count. -/
theorem reads_ov {p : BPair} {u v n : Nat}
    (h : reads p u v) (hn : u = n + v) :
    p.oneValue (BPair.ofNat n) := by
  refine BPair.oneValue_trans h ?_
  rw [
    ofNat_pair n]
  show (⟨u + 0 + 1⟩ : Pos) = ⟨n + v + 1⟩
  rw [
    hn]

/-- A constant list's evaluation is its own count. -/
theorem constRead (C d : Nat) :
    (eval [BPair.ofNat C] (BPair.ofNat d)).oneValue (BPair.ofNat C) := by
  have h : reads (BPair.ofNat C + BPair.ofNat d * BPair.unit)
      (C + d * 0) (0 + d * 0) := by
    rw [ofNat_pair C]
    exact reads_step reads_unit C 0 d
  refine reads_ov h ?_
  rw [Nat.mul_zero d, Nat.add_zero C]

/-- A linear factor's evaluation at a count: the stated gap of
members against the argument's own scale of the top count. -/
theorem linRead (X Y c n d : Nat) (h : Y + n = X + d * c) :
    (eval [⟨posOfSucc X, posOfSucc Y⟩, BPair.ofNat c]
      (BPair.ofNat d)).oneValue (BPair.ofNat n) := by
  have h1 : reads (BPair.ofNat c + BPair.ofNat d * BPair.unit)
      (c + d * 0) (0 + d * 0) := by
    rw [ofNat_pair c]
    exact reads_step reads_unit c 0 d
  refine reads_ov (reads_step h1 X Y d) ?_
  rw [Nat.mul_zero d, Nat.add_zero c, Nat.zero_add 0, Nat.mul_zero d,
    Nat.add_zero Y]
  exact h.symm.trans (Nat.add_comm Y n)

/-- An accumulating pass whose steps carry the read at every member
carries it to its end. -/
theorem eval_fold {α : Type} (r : BPair)
    (S : Poly → α → Poly) (T : Nat → α → Nat) (P : α → Prop)
    (hS : ∀ (acc : Poly) (n : Nat) (x : α), P x →
      (eval acc r).oneValue (BPair.ofNat n) →
      (eval (S acc x) r).oneValue (BPair.ofNat (T n x))) :
    ∀ (L : List α), (∀ x ∈ L, P x) →
      ∀ (acc : Poly) (n : Nat),
        (eval acc r).oneValue (BPair.ofNat n) →
        (eval (L.foldl S acc) r).oneValue (BPair.ofNat (L.foldl T n))
  | [], _, _, _, h => h
  | x :: t, hL, acc, n, h =>
    eval_fold r S T P hS t (fun y hy => hL y (List.Mem.tail x hy))
      (S acc x) (T n x) (hS acc n x (hL x (List.Mem.head t)) h)

/-- One product step carries the read. -/
theorem eval_mulStep {r : BPair} {f : Poly} {v : Nat}
    (hf : (eval f r).oneValue (BPair.ofNat v))
    (acc : Poly) (n : Nat)
    (h : (eval acc r).oneValue (BPair.ofNat n)) :
    (eval (mul acc f) r).oneValue (BPair.ofNat (n * v)) :=
  BPair.oneValue_trans (eval_mul acc f r)
    (BPair.oneValue_trans (BPair.mul_congr h hf)
      (BPair.oneValue_symm (BPair.ofNat_mul n v)))

/-! The derivative is additive. -/

theorem derivFrom_add : ∀ (n : Pos) (p q : Poly),
    derivFrom n (add p q) = add (derivFrom n p) (derivFrom n q)
  | _, [], _ => rfl
  | _, _ :: _, [] => rfl
  | n, c :: p, d :: q => by
    show ((c + d).scale n) :: derivFrom (succ n) (add p q)
      = (c.scale n + d.scale n) :: add (derivFrom (succ n) p)
        (derivFrom (succ n) q)
    rw [BPair.scale_add, derivFrom_add (succ n) p q]

theorem deriv_add : ∀ p q : Poly,
    deriv (add p q) = add (deriv p) (deriv q)
  | [], _ => rfl
  | c :: p, [] => by
    show deriv (add (c :: p) []) = add (deriv (c :: p)) []
    rw [add_nil, add_nil]
  | _ :: p, _ :: q => derivFrom_add .one p q

/-! The one-value read is a class read. -/

theorem oneValue_refl : ∀ p : Poly, oneValue p p
  | [] => trivial
  | c :: p => ⟨BPair.oneValue_refl c, oneValue_refl p⟩

/-- The class read at an equality: one value off the literal. -/
theorem oneValue_of_eq {u v : Poly} (h : u = v) : oneValue u v :=
  h ▸ oneValue_refl u

theorem oneValue_symm : ∀ {p q : Poly}, oneValue p q → oneValue q p
  | [], [], h => h
  | [], _ :: _, h => h
  | _ :: _, [], h => h
  | _ :: _, _ :: _, h =>
    ⟨BPair.oneValue_symm h.1, oneValue_symm h.2⟩

theorem unitTail_oneValue : ∀ {p q : Poly},
    unitTail p → unitTail q → oneValue p q
  | [], _, _, hq => hq
  | _ :: _, [], hp, _ => hp
  | _ :: _, _ :: _, hp, hq =>
    ⟨BPair.oneValue_trans hp.1 (BPair.oneValue_symm hq.1),
      unitTail_oneValue hp.2 hq.2⟩

theorem oneValue_unitTail : ∀ {p q : Poly},
    oneValue p q → unitTail q → unitTail p
  | [], _, _, _ => trivial
  | _ :: _, [], h, _ => h
  | _ :: _, _ :: _, h, hq =>
    ⟨BPair.oneValue_trans h.1 hq.1, oneValue_unitTail h.2 hq.2⟩

theorem unitTail_oneValue_right : ∀ {q r : Poly},
    unitTail q → oneValue q r → unitTail r
  | [], _, _, h => h
  | _ :: _, [], _, _ => trivial
  | _ :: _, _ :: _, hq, h =>
    ⟨BPair.oneValue_trans (BPair.oneValue_symm h.1) hq.1,
      unitTail_oneValue_right hq.2 h.2⟩

theorem oneValue_trans : ∀ {p q r : Poly},
    oneValue p q → oneValue q r → oneValue p r
  | [], _, _, h1, h2 => unitTail_oneValue_right h1 h2
  | _ :: _, [], _, h1, h2 => unitTail_oneValue h1 h2
  | _ :: _, _ :: _, [], h1, h2 => oneValue_unitTail h1 h2
  | _ :: _, _ :: _, _ :: _, h1, h2 =>
    ⟨BPair.oneValue_trans h1.1 h2.1, oneValue_trans h1.2 h2.2⟩

/-- The one-value read splits over a join at a matched seam. -/
theorem oneValue_append : ∀ (p p' q q' : Poly),
    p.length = p'.length → oneValue p p' → oneValue q q' →
    oneValue (p ++ q) (p' ++ q')
  | [], [], _, _, _, _, hq => hq
  | [], _ :: _, _, _, hl, _, _ => nomatch hl
  | _ :: _, [], _, _, hl, _, _ => nomatch hl
  | _ :: p, _ :: p', q, q', hl, hp, hq =>
    ⟨hp.1, oneValue_append p p' q q' (Nat.succ.inj hl) hp.2 hq⟩

/-- Two pointwise one-value maps read one value over any index
family. -/
theorem oneValue_map {α : Type} (f g : α → BPair) :
    ∀ l : List α, (∀ a ∈ l, (f a).oneValue (g a)) →
      oneValue (l.map f) (l.map g)
  | [], _ => trivial
  | a :: t, h =>
    ⟨h a (List.Mem.head t),
     oneValue_map f g t (fun x hx => h x (List.Mem.tail a hx))⟩

/-- The mapped family at the unit family, one member read at a
time. -/
theorem unitTail_map {α : Type} (f : α → BPair) :
    ∀ l : List α, (∀ a ∈ l, (f a).oneValue BPair.unit) →
      unitTail (l.map f)
  | [], _ => trivial
  | a :: t, h =>
    ⟨h a (List.Mem.head t),
     unitTail_map f t (fun x hx => h x (List.Mem.tail a hx))⟩

/-- A unit-family list reads every member at the unit, the mapped
family's converse. -/
theorem unitTail_member :
    ∀ {l : Poly}, unitTail l → ∀ x ∈ l, x.oneValue BPair.unit
  | [], _, _, h => nomatch h
  | _ :: t, hu, x, hx => by
    have hu' : _ ∧ unitTail t := hu
    cases hx with
    | head => exact hu'.1
    | tail _ hm => exact unitTail_member hu'.2 x hm

/-! The stated reads at the division and the roots. -/

/-- The top key's entry at any entry carrier, the unit at the
vacant list. -/
def topO {γ : Type} (ops : DOps γ) : List γ → γ
  | [] => ops.unit
  | c :: [] => c
  | _ :: c :: t => topO ops (c :: t)

/-- The top key's coefficient, the unit at the length-gauge tail. -/
def top : Poly → BPair := topO bpairOps

/-- The top key's entry at a stated list is its last member, the
length-gauge read of the top. -/
theorem topO_getAt {γ : Type} (ops : DOps γ) :
    ∀ (p : List γ) (n : Nat), p.length = n + 1 →
    topO ops p = ground.getAt ops.unit p n
  | [], _, h => Nat.noConfusion h
  | [_], 0, _ => rfl
  | [_], _ + 1, h => Nat.noConfusion (Nat.succ.inj h)
  | _ :: _ :: _, 0, h => Nat.noConfusion (Nat.succ.inj h)
  | _ :: c :: t, n + 1, h => topO_getAt ops (c :: t) n (Nat.succ.inj h)

/-! The descent's pair is one value at every solution.  The kit below
is that theorem's own plumbing — the coefficient reads of the sum, the
shift and the join, the descent's recursion unfolded at its fuel —
and stays private to it. -/

private theorem scale_unit {a : BPair} (h : a.oneValue BPair.unit) (x : BPair) :
    (a * x).oneValue BPair.unit :=
  BPair.oneValue_trans (BPair.mul_congr h (BPair.oneValue_refl x))
    (BPair.unit_mul x)

private theorem bp_cancel {x y z w : BPair} (h : (x + z).oneValue (y + w))
    (hx : x.oneValue y) : z.oneValue w := by
  have h1 : x.fst + z.fst + (y.snd + w.snd) = y.fst + w.fst + (x.snd + z.snd) := h
  have h2 : x.fst + y.snd = y.fst + x.snd := hx
  show z.fst + w.snd = w.fst + z.snd
  apply ground.add_right_cancel (c := x.fst + y.snd)
  calc z.fst + w.snd + (x.fst + y.snd)
      = x.fst + z.fst + (y.snd + w.snd) := by
        rw [ground.add_add_comm z.fst w.snd x.fst y.snd,
          ground.add_comm z.fst x.fst, ground.add_comm w.snd y.snd]
    _ = y.fst + w.fst + (x.snd + z.snd) := h1
    _ = w.fst + z.snd + (y.fst + x.snd) := by
        rw [ground.add_add_comm w.fst z.snd y.fst x.snd,
          ground.add_comm w.fst y.fst, ground.add_comm z.snd x.snd]
    _ = w.fst + z.snd + (x.fst + y.snd) := by rw [h2]

/-! The coefficient reads: the one-value class is the keyed read. -/

/-- A list whose every key reads the unit is unit-tailed, the keyed
read's converse. -/
theorem unitTail_of_getAt : ∀ {p : Poly},
    (∀ k : Nat, (getAt BPair.unit p k).oneValue BPair.unit) → unitTail p
  | [], _ => trivial
  | _ :: _, h => ⟨h 0, unitTail_of_getAt (fun k => h (k + 1))⟩

/-- A unit tail's entry reads the unit at every key, the keys
beyond the top included. -/
theorem getAt_unitTail : ∀ {p : Poly}, unitTail p → ∀ k : Nat,
    (getAt BPair.unit p k).oneValue BPair.unit
  | [], _, _ => BPair.oneValue_refl _
  | _ :: _, h, 0 => h.1
  | _ :: _, h, k + 1 => getAt_unitTail h.2 k

/-- A list off the unit tail exhibits an occupied key inside its
count. -/
theorem offUnit_witness : ∀ u : List BPair,
    ¬ unitTail u →
    ∃ p, p < u.length
      ∧ ¬ (ground.getAt BPair.unit u p).oneValue BPair.unit
  | [], h => absurd trivial h
  | c :: u, h => by
    by_cases hc : c.oneValue BPair.unit
    · have hu : ¬ unitTail u := fun ht => h ⟨hc, ht⟩
      obtain ⟨p, hp, hoff⟩ := offUnit_witness u hu
      exact ⟨p + 1, Nat.succ_lt_succ hp, hoff⟩
    · exact ⟨0, Nat.succ_pos _, hc⟩

/-- A one-value read is one value at every key. -/
theorem oneValue_getAt : ∀ (k : Nat) {p q : Poly}, oneValue p q →
    (getAt BPair.unit p k).oneValue (getAt BPair.unit q k)
  | 0, [], [], _ => BPair.oneValue_refl _
  | 0, [], _ :: _, h => BPair.oneValue_symm h.1
  | 0, _ :: _, [], h => h.1
  | 0, _ :: _, _ :: _, h => h.1
  | _ + 1, [], [], _ => BPair.oneValue_refl _
  | k + 1, [], _ :: _, h => oneValue_getAt k (p := []) h.2
  | k + 1, _ :: _, [], h => oneValue_getAt k (q := []) (unitTail_oneValue h.2 trivial)
  | k + 1, _ :: _, _ :: _, h => oneValue_getAt k h.2

/-- A leading part keeps a unit tail. -/
private theorem unitTail_take : ∀ (k : Nat) {p : Poly},
    unitTail p → unitTail (p.take k)
  | 0, _, _ => trivial
  | _ + 1, [], _ => trivial
  | k + 1, _ :: _, h => ⟨h.1, unitTail_take k h.2⟩

/-- A dropped part keeps a unit tail. -/
private theorem unitTail_drop : ∀ (k : Nat) {p : Poly},
    unitTail p → unitTail (p.drop k)
  | 0, _, h => h
  | _ + 1, [], _ => trivial
  | k + 1, _ :: _, h => unitTail_drop k h.2

/-- The leading part moves across the one-value read, key by
key. -/
theorem take_congr : ∀ (k : Nat) {p q : Poly}, oneValue p q →
    oneValue (p.take k) (q.take k)
  | 0, _, _, _ => trivial
  | k + 1, [], _, h => unitTail_take (k + 1) h
  | k + 1, _ :: _, [], h => ⟨h.1, unitTail_take k h.2⟩
  | k + 1, _ :: _, _ :: _, h => ⟨h.1, take_congr k h.2⟩

/-- The dropped part moves across the one-value read, key by
key. -/
theorem drop_congr : ∀ (k : Nat) {p q : Poly}, oneValue p q →
    oneValue (p.drop k) (q.drop k)
  | 0, _, _, h => h
  | k + 1, [], _, h => unitTail_drop (k + 1) h
  | k + 1, _ :: _, [], h =>
    unitTail_oneValue (unitTail_drop k h.2) trivial
  | k + 1, _ :: _, _ :: _, h => drop_congr k h.2

/-- A list at a value-one top reads its own monic display: below
the top the display is the list's entries, and at the top the
scalar one reads the top's value. -/
theorem monic_dropLast_oneValue (p : Poly) (n : Nat)
    (hl : p.length = n + 1)
    (ht : (ground.getAt BPair.unit p n).oneValue (BPair.ofPos Pos.one)) :
    oneValue (monic p.dropLast) p :=
  match p, n, hl, ht with
  | [], _, hl, _ => Nat.noConfusion hl
  | [_], 0, _, ht => ⟨BPair.oneValue_symm ht, trivial⟩
  | [_], _ + 1, hl, _ => Nat.noConfusion (Nat.succ.inj hl)
  | _ :: _ :: _, 0, hl, _ => Nat.noConfusion (Nat.succ.inj hl)
  | c :: d :: t, n + 1, hl, ht =>
    ⟨BPair.oneValue_refl c,
      monic_dropLast_oneValue (d :: t) n (Nat.succ.inj hl) ht⟩

/-- Keywise one-value reads collect to the polynomials' own. -/
theorem ov_of_getAt : ∀ {p q : Poly},
    (∀ k : Nat, (getAt BPair.unit p k).oneValue (getAt BPair.unit q k)) →
    oneValue p q
  | [], _, h => unitTail_of_getAt (fun k => BPair.oneValue_symm (h k))
  | _ :: _, [], h => unitTail_of_getAt h
  | _ :: _, _ :: _, h => ⟨h 0, ov_of_getAt (fun k => h (k + 1))⟩

/-- Two coordinate families at matched lengths whose every entry
reads one value read one value as polynomials, the entrywise
build of the coordinate equivalence. -/
theorem oneValue_of_entries : ∀ u v : List BPair,
    u.length = v.length →
    (∀ t, t < u.length →
      (getAt BPair.unit u t).oneValue (getAt BPair.unit v t)) →
    oneValue u v
  | [], [], _, _ => True.intro
  | [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, [], h, _ => Nat.noConfusion h
  | _ :: u', _ :: v', h, hent =>
    And.intro (hent 0 (Nat.succ_pos _))
      (oneValue_of_entries u' v' (Nat.succ.inj h)
        (fun t ht => hent (t + 1) (Nat.succ_lt_succ ht)))

/-- The sum's key read at any entry carrier is the keys' sum, at a
read reflexive and symmetric with the sum's unit its unit on either
side. -/
theorem getAt_addLO {γ : Type} (ops : DOps γ) (R : DRead γ)
    (hrefl : ∀ x, R.rel x x) (hsymm : ∀ {x y}, R.rel x y → R.rel y x)
    (hunitAdd : ∀ x, R.rel (ops.add ops.unit x) x)
    (haddUnit : ∀ x, R.rel (ops.add x ops.unit) x) :
    ∀ (p q : List γ) (k : Nat),
      R.rel (ground.getAt ops.unit (addLO ops p q) k)
        (ops.add (ground.getAt ops.unit p k) (ground.getAt ops.unit q k))
  | [], _, _ => hsymm (hunitAdd _)
  | _ :: _, [], _ => hsymm (haddUnit _)
  | _ :: _, _ :: _, 0 => hrefl _
  | _ :: p, _ :: q, k + 1 => getAt_addLO ops R hrefl hsymm hunitAdd haddUnit p q k

/-- A scaled list's key read at any entry carrier is the key's
scale, at a read where a factor against the sum's unit reads the
unit. -/
theorem getAt_mapMul {γ : Type} (ops : DOps γ) (R : DRead γ)
    (hrefl : ∀ x, R.rel x x) (hsymm : ∀ {x y}, R.rel x y → R.rel y x)
    (hmulUnit : ∀ x, R.rel (ops.mul x ops.unit) ops.unit) (c : γ) :
    ∀ (l : List γ) (k : Nat),
      R.rel (ground.getAt ops.unit (l.map (ops.mul c)) k)
        (ops.mul c (ground.getAt ops.unit l k))
  | [], _ => hsymm (hmulUnit c)
  | _ :: _, 0 => hrefl _
  | _ :: l, k + 1 => getAt_mapMul ops R hrefl hsymm hmulUnit c l k

/-- The partner list's key read at any entry carrier is the key's
partner, at a read where the unit's partner reads the unit. -/
theorem getAt_mapSwap {γ : Type} (ops : DOps γ) (R : DRead γ)
    (hrefl : ∀ x, R.rel x x) (hsymm : ∀ {x y}, R.rel x y → R.rel y x)
    (hswapUnit : R.rel (ops.swap ops.unit) ops.unit) :
    ∀ (q : List γ) (k : Nat),
      R.rel (ground.getAt ops.unit (q.map ops.swap) k)
        (ops.swap (ground.getAt ops.unit q k))
  | [], _ => hsymm hswapUnit
  | _ :: _, 0 => hrefl _
  | _ :: q, k + 1 => getAt_mapSwap ops R hrefl hsymm hswapUnit q k

/-- The sum's key read is the keys' sum. -/
theorem getAt_add : ∀ (p q : Poly) (k : Nat),
    (getAt BPair.unit (add p q) k).oneValue
      (getAt BPair.unit p k + getAt BPair.unit q k)
  | [], _, _ => BPair.oneValue_symm (BPair.unit_add _)
  | _ :: _, [], _ => BPair.oneValue_symm (BPair.add_unit _)
  | _ :: _, _ :: _, 0 => BPair.oneValue_refl _
  | _ :: p, _ :: q, k + 1 => getAt_add p q k

/-- A scaled list's key read is the key's scale. -/
theorem getAt_scale (c : BPair) : ∀ (l : Poly) (k : Nat),
    (getAt BPair.unit (l.map (fun d => c * d)) k).oneValue
      (c * getAt BPair.unit l k)
  | [], _ => BPair.oneValue_symm (BPair.mul_unit c)
  | _ :: _, 0 => BPair.oneValue_refl _
  | _ :: l, k + 1 => getAt_scale c l k

/-! The componentwise sum's algebra, read at the keys. -/

theorem add_congr {p q p' q' : Poly} (h1 : oneValue p p')
    (h2 : oneValue q q') : oneValue (add p q) (add p' q') :=
  ov_of_getAt (fun k =>
    BPair.oneValue_trans (getAt_add p q k)
      (BPair.oneValue_trans
        (BPair.add_congr (oneValue_getAt k h1) (oneValue_getAt k h2))
        (BPair.oneValue_symm (getAt_add p' q' k))))

theorem add_cancel {a b a' b' : Poly}
    (h : oneValue (add a b) (add a' b')) (ha : oneValue a a') : oneValue b b' :=
  ov_of_getAt (fun k => bp_cancel
    (BPair.oneValue_trans (BPair.oneValue_symm (getAt_add a b k))
      (BPair.oneValue_trans (oneValue_getAt k h) (getAt_add a' b' k)))
    (oneValue_getAt k ha))

theorem add_shuffle (a b c d : Poly) :
    oneValue (add (add a b) (add c d)) (add (add a c) (add b d)) :=
  ov_of_getAt (fun k =>
    BPair.oneValue_trans (getAt_add (add a b) (add c d) k)
      (BPair.oneValue_trans
        (BPair.add_congr (getAt_add a b k) (getAt_add c d k))
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (BPair.add_add_comm _ _ _ _))
          (BPair.oneValue_trans
            (BPair.add_congr (BPair.oneValue_symm (getAt_add a c k))
              (BPair.oneValue_symm (getAt_add b d k)))
            (BPair.oneValue_symm (getAt_add (add a c) (add b d) k))))))

theorem add_join (a b c : Poly) :
    oneValue (add a (add b c)) (add (add a b) c) :=
  ov_of_getAt (fun k =>
    BPair.oneValue_trans (getAt_add a (add b c) k)
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) (getAt_add b c k))
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (BPair.add_assoc _ _ _).symm)
          (BPair.oneValue_trans
            (BPair.add_congr (BPair.oneValue_symm (getAt_add a b k))
              (BPair.oneValue_refl _))
            (BPair.oneValue_symm (getAt_add (add a b) c k))))))

theorem add_swap3 (a b c : Poly) :
    oneValue (add (add a b) c) (add (add a c) b) := by
  have h := add_shuffle a b c []
  rw [add_nil c, add_nil b] at h
  exact h

theorem unitTail_add {p : Poly} (h : unitTail p) (q : Poly) :
    oneValue (add p q) q :=
  ov_of_getAt (fun k =>
    BPair.oneValue_trans (getAt_add p q k)
      (BPair.oneValue_trans
        (BPair.add_congr (getAt_unitTail h k) (BPair.oneValue_refl _))
        (BPair.unit_add _)))

theorem add_unitTail (p : Poly) {q : Poly} (h : unitTail q) :
    oneValue (add p q) p :=
  ov_of_getAt (fun k =>
    BPair.oneValue_trans (getAt_add p q k)
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) (getAt_unitTail h k))
        (BPair.add_unit _)))

/-- Two unit tails join to a unit tail. -/
theorem unitTail_sum {p q : Poly} (hp : unitTail p) (hq : unitTail q) :
    unitTail (add p q) :=
  oneValue_unitTail (unitTail_add hp q) hq

private theorem add_len : ∀ (p q : Poly), p.length = q.length →
    (add p q).length = p.length
  | [], [], _ => rfl
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | _ :: p, _ :: q, h => by
    show (add p q).length + 1 = p.length + 1
    rw [add_len p q (ground.addCancelR 1 h)]

theorem add_len_le : ∀ (p q : Poly) (n : Nat), p.length ≤ n →
    q.length ≤ n → (add p q).length ≤ n
  | [], _, _, _, hq => hq
  | _ :: _, [], _, hp, _ => hp
  | _ :: _, _ :: _, 0, hp, _ => absurd hp (Nat.not_succ_le_zero _)
  | _ :: p, _ :: q, n + 1, hp, hq =>
    Nat.succ_le_succ (add_len_le p q n (Nat.le_of_succ_le_succ hp)
      (Nat.le_of_succ_le_succ hq))

private theorem add_snoc : ∀ (p q : Poly), p.length = q.length →
    ∀ z : BPair, add p (q ++ [z]) = add p q ++ [z]
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, [], h, _ => Nat.noConfusion h
  | a :: p, b :: q, h, z => by
    show (a + b) :: add p (q ++ [z]) = (a + b) :: (add p q ++ [z])
    rw [add_snoc p q (ground.addCancelR 1 h) z]

private theorem add_split : ∀ (p q : Poly), p.length = q.length →
    ∀ u v : Poly, add (p ++ u) (q ++ v) = add p q ++ add u v
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => Nat.noConfusion h
  | _ :: _, [], h, _, _ => Nat.noConfusion h
  | a :: p, b :: q, h, u, v => by
    show (a + b) :: add (p ++ u) (q ++ v) = (a + b) :: (add p q ++ add u v)
    rw [add_split p q (ground.addCancelR 1 h) u v]

private theorem ov_split : ∀ {p q : Poly}, p.length = q.length → oneValue p q →
    ∀ {u v : Poly}, oneValue u v → oneValue (p ++ u) (q ++ v)
  | [], [], _, _, _, _, hu => hu
  | [], _ :: _, h, _, _, _, _ => Nat.noConfusion h
  | _ :: _, [], h, _, _, _, _ => Nat.noConfusion h
  | _ :: _, _ :: _, h, hpq, _, _, hu =>
    ⟨hpq.1, ov_split (ground.addCancelR 1 h) hpq.2 hu⟩

private theorem unitTail_join : ∀ {u : Poly}, unitTail u → ∀ {v : Poly},
    unitTail v → unitTail (u ++ v)
  | [], _, _, hv => hv
  | _ :: _, hu, _, hv => ⟨hu.1, unitTail_join hu.2 hv⟩

/-! The key shift, the join's read and the member swap. -/

/-- The sum's length at a second member no longer than the first:
the first member's own. -/
theorem add_lenL : ∀ p q : Poly, q.length ≤ p.length →
    (add p q).length = p.length
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: _, [], _ => rfl
  | _ :: p, _ :: q, h => by
    show (add p q).length + 1 = p.length + 1
    rw [add_lenL p q (Nat.le_of_succ_le_succ h)]

/-- The sum's length at a first member no longer than the second:
the second member's own. -/
theorem add_lenR : ∀ p q : Poly, p.length ≤ q.length →
    (add p q).length = q.length
  | [], _, _ => rfl
  | _ :: _, [], h => absurd h (Nat.not_succ_le_zero _)
  | _ :: p, _ :: q, h => by
    show (add p q).length + 1 = q.length + 1
    rw [add_lenR p q (Nat.le_of_succ_le_succ h)]

/-- The convolution's length at the factors' own: the degrees add,
the vacant factor's product vacant. -/
theorem mul_len_le : ∀ (p q : Poly) (a b : Nat),
    p.length ≤ a + 1 → q.length ≤ b + 1 →
    (mul p q).length ≤ a + b + 1
  | [], _, _, _, _, _ => Nat.zero_le _
  | c :: p, q, a, b, hp, hq => by
    show (add (q.map (fun d => c * d))
      (BPair.unit :: mul p q)).length ≤ a + b + 1
    refine add_len_le _ _ _ ?_ ?_
    · rw [ground.length_map]
      exact Nat.le_trans hq (Nat.le_add_left (b + 1) a)
    · show (mul p q).length + 1 ≤ a + b + 1
      cases a with
      | zero =>
        cases p with
        | nil =>
          show 0 + 1 ≤ 0 + b + 1
          exact Nat.succ_le_succ (Nat.zero_le _)
        | cons x s =>
          exact absurd (Nat.le_of_succ_le_succ hp)
            (Nat.not_succ_le_zero s.length)
      | succ a' =>
        have hIH := mul_len_le p q a' b
          (Nat.le_of_succ_le_succ hp) hq
        have he : a' + 1 + b + 1 = a' + b + 1 + 1 := by
          rw [Nat.add_right_comm a' 1 b]
        rw [he]
        exact Nat.succ_le_succ hIH

/-- The key shift: the coefficient list moved up by a natural key,
the vacated places the sum's unit. -/
def shiftUp : Nat → Poly → Poly
  | 0, p => p
  | n + 1, p => BPair.unit :: shiftUp n p

/-- The shift's key count: the vacated places joined to the
list's own. -/
theorem len_shift : ∀ (n : Nat) (p : Poly),
    (shiftUp n p).length = n + p.length
  | 0, _ => (Nat.zero_add _).symm
  | n + 1, p => by
    show (shiftUp n p).length + 1 = n + 1 + p.length
    rw [len_shift n p, Nat.add_right_comm]

private theorem shift_append : ∀ (n : Nat) (p q : Poly),
    shiftUp n (p ++ q) = shiftUp n p ++ q
  | 0, _, _ => rfl
  | n + 1, p, q => by
    show BPair.unit :: shiftUp n (p ++ q) = BPair.unit :: (shiftUp n p ++ q)
    rw [shift_append n p q]

/-- The shift composes additively. -/
theorem shiftUp_shiftUp : ∀ (a b : Nat) (p : Poly),
    shiftUp a (shiftUp b p) = shiftUp (a + b) p
  | 0, b, p => by rw [Nat.zero_add]; rfl
  | a + 1, b, p => by
    show BPair.unit :: shiftUp a (shiftUp b p) = shiftUp (a + 1 + b) p
    rw [shiftUp_shiftUp a b p, Nat.succ_add a b]
    rfl

/-- The shift reads a sum's shift memberwise. -/
theorem shiftUp_add : ∀ (c : Nat) (p q : Poly),
    oneValue (shiftUp c (add p q)) (add (shiftUp c p) (shiftUp c q))
  | 0, p, q => oneValue_refl _
  | c + 1, p, q => by
    show oneValue (BPair.unit :: shiftUp c (add p q))
      ((BPair.unit + BPair.unit) :: add (shiftUp c p) (shiftUp c q))
    exact ⟨by decide +kernel, shiftUp_add c p q⟩

private theorem shift_cons (n : Nat) (q : Poly) :
    shiftUp n (BPair.unit :: q) = BPair.unit :: shiftUp n q := by
  show shiftUp n (shiftUp 1 q) = shiftUp 1 (shiftUp n q)
  rw [shiftUp_shiftUp n 1 q, shiftUp_shiftUp 1 n q,
    Nat.add_comm n 1]

/-- A key below the shift reads the shifted list at the sum's
unit. -/
theorem getAt_shiftUp_lt : ∀ (n : Nat) (p : Poly) (k : Nat), k < n →
    getAt BPair.unit (shiftUp n p) k = BPair.unit
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, 0, _ => rfl
  | n + 1, p, k + 1, h => getAt_shiftUp_lt n p k (Nat.lt_of_succ_lt_succ h)

/-- A key at or beyond the shift reads the shifted list at the
source's own key. -/
theorem getAt_shiftUp_add : ∀ (n : Nat) (p : Poly) (k : Nat),
    getAt BPair.unit (shiftUp n p) (n + k) = getAt BPair.unit p k
  | 0, _, k => by rw [Nat.zero_add k]; rfl
  | n + 1, p, k => by
    rw [Nat.add_right_comm n 1 k]
    show getAt BPair.unit (shiftUp n p) (n + k) = getAt BPair.unit p k
    exact getAt_shiftUp_add n p k

/-- A unit-tail list keeps its unit tail across the key shift. -/
theorem unitTail_shiftUp : ∀ (n : Nat) {p : Poly}, unitTail p →
    unitTail (shiftUp n p)
  | 0, _, h => h
  | n + 1, _, h => ⟨BPair.oneValue_refl _, unitTail_shiftUp n h⟩

/-- The key shift's one-value congruence. -/
theorem shiftUp_ov : ∀ (n : Nat) {x y : Poly}, oneValue x y →
    oneValue (shiftUp n x) (shiftUp n y)
  | 0, _, _, h => h
  | n + 1, _, _, h => ⟨BPair.oneValue_refl _, shiftUp_ov n h⟩

private theorem append_add : ∀ (p q : Poly),
    oneValue (p ++ q) (add p (shiftUp p.length q))
  | [], _ => oneValue_refl _
  | c :: p, q =>
    ⟨BPair.oneValue_symm (BPair.add_unit c), append_add p q⟩

theorem append_unit (p : Poly) {v : Poly} (h : unitTail v) :
    oneValue (p ++ v) p :=
  oneValue_trans (append_add p v) (add_unitTail p (unitTail_shiftUp p.length h))

/-- The memberwise swap entrywise, the negation read at the balance
pairs. -/
def neg : Poly → Poly := polyOps.swap

/-- The vacant content is its own negation, the unit's swap read
entrywise. -/
theorem neg_repl (n : Nat) :
    neg (List.replicate n BPair.unit)
      = List.replicate n BPair.unit := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show BPair.unit.swap :: neg (List.replicate m BPair.unit)
      = BPair.unit :: List.replicate m BPair.unit
    rw [ih]
    rfl

/-- The memberwise representative entrywise, the normal spelling of
every coefficient. -/
def pnorm (p : Poly) : Poly := p.map BPair.norm

/-- The representative list reads one value with its own, member by
member. -/
theorem pnorm_oneValue : ∀ u : Poly, oneValue (pnorm u) u
  | [] => trivial
  | a :: u => ⟨BPair.norm_oneValue a, pnorm_oneValue u⟩

/-- The representative list keeps the order. -/
theorem pnorm_length (u : Poly) : (pnorm u).length = u.length :=
  ground.length_map _ u

/-- One value in, one representative list out: the memberwise
representative is a function of the members' values alone. -/
theorem pnorm_congr : ∀ u w : Poly, u.length = w.length →
    oneValue u w → pnorm u = pnorm w
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => Nat.noConfusion hl
  | _ :: _, [], hl, _ => Nat.noConfusion hl
  | a :: u, b :: w, hl, h => by
    show a.norm :: pnorm u = b.norm :: pnorm w
    rw [BPair.norm_congr h.1, pnorm_congr u w (Nat.succ.inj hl) h.2]

/-- The representative list is its own. -/
theorem pnorm_pnorm : ∀ u : Poly, pnorm (pnorm u) = pnorm u
  | [] => rfl
  | a :: u => by
    show (a.norm).norm :: pnorm (pnorm u) = a.norm :: pnorm u
    rw [BPair.norm_congr (BPair.norm_oneValue a), pnorm_pnorm u]

/-- The length gauge's tail dropped at the value test, the
occupancy family read to its top. -/
private def trim : Poly → Poly
  | [] => []
  | c :: t =>
    match trim t with
    | [] => if decide (c.oneValue BPair.unit) then [] else [c]
    | d :: t' => c :: d :: t'

/-- The value's one representative: the memberwise representatives
with the length gauge's tail dropped — the occupancy family at its
top, the largest key at a coefficient off the sum's unit. -/
def vnorm (P : Poly) : Poly := trim (pnorm P)

/-- A unit tail's value has the vacant representative. -/
private theorem vnorm_unitTail : ∀ {P : Poly}, unitTail P → vnorm P = []
  | [], _ => rfl
  | c :: p, h => by
    show (match trim (pnorm p) with
      | [] => if decide ((BPair.norm c).oneValue BPair.unit) then []
              else [BPair.norm c]
      | d :: t' => BPair.norm c :: d :: t') = []
    rw [show trim (pnorm p) = [] from vnorm_unitTail h.2,
        show BPair.norm c = BPair.unit from
          (BPair.norm_congr h.1).trans (by rfl)]
    rfl

/-- One value in, one representative out: the value's
representative is a function of the one-value class alone, at
every pair of representatives. -/
theorem vnorm_congr : ∀ {P Q : Poly}, oneValue P Q → vnorm P = vnorm Q
  | [], q, h => (vnorm_unitTail (show unitTail q from h)).symm
  | c :: p, [], h =>
    vnorm_unitTail (show unitTail (c :: p) from ⟨h.1, h.2⟩)
  | c :: p, d :: q, h => by
    show (match trim (pnorm p) with
      | [] => if decide ((BPair.norm c).oneValue BPair.unit) then []
              else [BPair.norm c]
      | e :: t' => BPair.norm c :: e :: t')
      = (match trim (pnorm q) with
      | [] => if decide ((BPair.norm d).oneValue BPair.unit) then []
              else [BPair.norm d]
      | e :: t' => BPair.norm d :: e :: t')
    rw [show trim (pnorm p) = trim (pnorm q) from vnorm_congr h.2,
        BPair.norm_congr h.1]

/-- The length gauge's dropped tail reads one value with its own
list: every dropped key sits at the sum's unit. -/
private theorem trim_ov : ∀ l : Poly, oneValue (trim l) l
  | [] => trivial
  | c :: t => by
    have ht := trim_ov t
    show oneValue (match trim t with
      | [] => if decide (c.oneValue BPair.unit) then [] else [c]
      | d :: t' => c :: d :: t') (c :: t)
    cases htr : trim t with
    | nil =>
      have hu : unitTail t := by
        rw [htr] at ht
        exact ht
      cases hc : decide (c.oneValue BPair.unit) with
      | true => exact ⟨of_decide_eq_true hc, hu⟩
      | false => exact ⟨BPair.oneValue_refl c, hu⟩
    | cons d t' =>
      refine ⟨BPair.oneValue_refl c, ?_⟩
      rw [htr] at ht
      exact ht

/-- The value's representative reads one value with its own
polynomial: the memberwise representatives and the dropped length
gauge each keep the value. -/
theorem vnorm_ov (P : Poly) : oneValue (vnorm P) P :=
  oneValue_trans (trim_ov (pnorm P)) (pnorm_oneValue P)

/-- The representative at an occupied tail: a further coefficient
enters as its own representative above the tail's. -/
theorem vnorm_cons_occ (c d : BPair) (p t : Poly)
    (h : vnorm p = d :: t) :
    vnorm (c :: p) = c.norm :: d :: t := by
  show (match trim (pnorm p) with
    | [] => if decide ((BPair.norm c).oneValue BPair.unit) then []
            else [BPair.norm c]
    | e :: t' => BPair.norm c :: e :: t') = c.norm :: d :: t
  rw [show trim (pnorm p) = d :: t from h]

/-- The representative at a vacant tail and an occupied
coefficient: the one-member list at the coefficient's
representative. -/
theorem vnorm_cons_off (c : BPair) (p : Poly) (h : vnorm p = [])
    (hc : ¬ c.oneValue BPair.unit) : vnorm (c :: p) = [c.norm] := by
  have hd : decide ((BPair.norm c).oneValue BPair.unit) = false :=
    decide_eq_false (fun hu => hc (BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.norm_oneValue c)) hu))
  show (match trim (pnorm p) with
    | [] => if decide ((BPair.norm c).oneValue BPair.unit) then []
            else [BPair.norm c]
    | e :: t' => BPair.norm c :: e :: t') = [c.norm]
  rw [show trim (pnorm p) = [] from h]
  show (if decide ((BPair.norm c).oneValue BPair.unit) then []
        else [BPair.norm c]) = [c.norm]
  rw [hd]
  rfl

/-- The Horner read at the memberwise swap: the negated
coefficients evaluate to the evaluation's own balance partner. -/
theorem eval_neg : ∀ (p : Poly) (r : BPair),
    eval (neg p) r = (eval p r).swap
  | [], _ => rfl
  | c :: p, r => by
    show c.swap + r * eval (neg p) r = (c + r * eval p r).swap
    rw [eval_neg p r, BPair.mul_swap, BPair.swap_add]

/-- The top key's coefficient at the memberwise swap. -/
theorem top_neg : ∀ l : Poly, top (neg l) = (top l).swap
  | [] => rfl
  | [_] => rfl
  | _ :: c :: t => top_neg (c :: t)

/-- A key sits at the sum's unit exactly where its balance partner
does, the decision read literally. -/
private theorem decide_swap_unit (c : BPair) :
    decide ((c.swap).oneValue BPair.unit)
      = decide (c.oneValue BPair.unit) := by
  cases hc : decide (c.oneValue BPair.unit) with
  | true =>
    exact decide_eq_true (show (c.swap).oneValue BPair.unit from
      ground.swap_congr (of_decide_eq_true hc))
  | false =>
    cases hs : decide ((c.swap).oneValue BPair.unit) with
    | true =>
      exact absurd ((decide_eq_true (show c.oneValue BPair.unit from
        ground.swap_congr (of_decide_eq_true hs))).symm.trans hc)
        (fun h => Bool.noConfusion h)
    | false => rfl

/-- The memberwise representatives commute with the memberwise
swap. -/
private theorem pnorm_neg : ∀ p : Poly, pnorm (neg p) = neg (pnorm p)
  | [] => rfl
  | c :: p => by
    show (c.swap).norm :: pnorm (neg p) = (c.norm).swap :: neg (pnorm p)
    rw [pnorm_neg p, BPair.norm_swap]

/-- The length gauge's dropped tail commutes with the memberwise
swap: a key sits at the sum's unit exactly where its partner
does. -/
private theorem trim_neg : ∀ l : Poly, trim (neg l) = neg (trim l)
  | [] => rfl
  | c :: t => by
    show (match trim (neg t) with
      | [] => if decide ((c.swap).oneValue BPair.unit) then []
              else [c.swap]
      | d :: t' => c.swap :: d :: t')
      = neg (match trim t with
      | [] => if decide (c.oneValue BPair.unit) then [] else [c]
      | d :: t' => c :: d :: t')
    rw [trim_neg t, decide_swap_unit c]
    cases htr : trim t with
    | nil =>
      cases hc : decide (c.oneValue BPair.unit) with
      | true => rfl
      | false => rfl
    | cons d t' => rfl

/-- The value's representative at the memberwise swap: the
representative of the negation is the negation of the
representative. -/
theorem vnorm_neg (P : Poly) : vnorm (neg P) = neg (vnorm P) := by
  unfold vnorm
  rw [pnorm_neg P, trim_neg (pnorm P)]

/-- The polynomial's entrywise rescaling at a pair, the scale
carried onto every coefficient at its representative. -/
def scaleP (c : BPair) (p : Poly) : Poly :=
  p.map (fun x => (c * x).norm)

/-- The one-member scale is the polynomial itself, the
representative read at every coefficient. -/
theorem scaleP_one : ∀ p : Poly,
    oneValue (scaleP (BPair.ofPos Pos.one) p) p
  | [] => trivial
  | x :: p =>
    ⟨BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.ofNat_one_mul x),
     scaleP_one p⟩

/-- The rescaling keeps the key count. -/
theorem length_scaleP (c : BPair) (p : Poly) :
    (scaleP c p).length = p.length :=
  ground.length_map _ p

/-- The scale reads at every key, the scalar against the key's
coefficient. -/
theorem getAt_scaleP (c : BPair) : ∀ (p : Poly) (k : Nat),
    (ground.getAt BPair.unit (scaleP c p) k).oneValue
      (c * ground.getAt BPair.unit p k)
  | [], _ => BPair.oneValue_symm (BPair.mul_unit c)
  | _ :: _, 0 => BPair.norm_oneValue _
  | _ :: t, k + 1 => getAt_scaleP c t k

/-- A scale at the sum's own unit rescales to a unit tail, the
scale swallowing every coefficient at its own value. -/
theorem scaleP_null {c : BPair} (h : c.oneValue BPair.unit) :
    ∀ p : Poly, unitTail (scaleP c p)
  | [] => trivial
  | x :: p =>
    ⟨BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans
        (BPair.mul_congr h (BPair.oneValue_refl x))
        (BPair.unit_mul x)),
      scaleP_null h p⟩

/-- The sum's unit scales a polynomial to a unit tail, the null
scale's own literal instance. -/
theorem scaleP_unit (p : Poly) : unitTail (scaleP BPair.unit p) :=
  scaleP_null (BPair.oneValue_refl BPair.unit) p

/-- A unit-tail list scales to a unit tail at every scalar. -/
theorem scaleP_unitTail (c : BPair) : ∀ p : Poly,
    unitTail p → unitTail (scaleP c p)
  | [], _ => trivial
  | _ :: t, h =>
    ⟨BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl c) h.1)
        (BPair.mul_unit c)),
     scaleP_unitTail c t h.2⟩

/-- The rescaling's congruence at its list, every shape. -/
theorem oneValue_scaleP (c : BPair) : ∀ {p p' : Poly},
    oneValue p p' → oneValue (scaleP c p) (scaleP c p')
  | [], p', h => scaleP_unitTail c p' h
  | _ :: t, [], h =>
    ⟨BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl c) h.1)
        (BPair.mul_unit c)),
     scaleP_unitTail c t h.2⟩
  | _ :: _, _ :: _, h =>
    ⟨BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl c) h.1)
        (BPair.oneValue_symm (BPair.norm_oneValue _))),
     oneValue_scaleP c h.2⟩

/-- Two scales' sum splits the rescaling, coefficient by
coefficient. -/
theorem scaleP_add (c d : BPair) : ∀ p : Poly,
    oneValue (scaleP (c + d) p) (add (scaleP c p) (scaleP d p))
  | [] => trivial
  | x :: p =>
    ⟨BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.right_distrib c d x))
        (BPair.add_congr (BPair.oneValue_symm (BPair.norm_oneValue _))
          (BPair.oneValue_symm (BPair.norm_oneValue _)))),
     scaleP_add c d p⟩

/-- The rescaling splits over the sum, coefficient by
coefficient. -/
theorem scaleP_sum (c : BPair) : ∀ p q : Poly,
    oneValue (scaleP c (add p q)) (add (scaleP c p) (scaleP c q))
  | [], _ => oneValue_refl _
  | _ :: _, [] => oneValue_refl _
  | a :: p, b :: q =>
    ⟨BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.left_distrib c a b))
        (BPair.add_congr (BPair.oneValue_symm (BPair.norm_oneValue _))
          (BPair.oneValue_symm (BPair.norm_oneValue _)))),
     scaleP_sum c p q⟩

/-- Two rescalings compose at the scales' own product. -/
theorem scaleP_mul (c d : BPair) : ∀ p : Poly,
    oneValue (scaleP c (scaleP d p)) (scaleP (c * d) p)
  | [] => trivial
  | a :: p =>
    ⟨BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl c)
          (BPair.norm_oneValue (d * a)))
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (BPair.mul_assoc c d a).symm)
          (BPair.oneValue_symm (BPair.norm_oneValue _)))),
     scaleP_mul c d p⟩

/-- The rescaling respects the scale's own class read. -/
theorem scaleP_congr {c d : BPair} (h : c.oneValue d) (p : Poly) :
    oneValue (scaleP c p) (scaleP d p) :=
  oneValue_map (fun x => (c * x).norm) (fun x => (d * x).norm) p
    (fun x _ => BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans (BPair.mul_congr h (BPair.oneValue_refl x))
        (BPair.oneValue_symm (BPair.norm_oneValue _))))

/-- A negated list's rescaling reads the rescaling's own negation. -/
theorem scaleP_neg (c : BPair) : ∀ p : Poly,
    oneValue (scaleP c (neg p)) (neg (scaleP c p))
  | [] => trivial
  | x :: p =>
    ⟨by
      show ((c * x.swap).norm).oneValue (((c * x).norm).swap)
      rw [BPair.mul_swap]
      exact BPair.oneValue_trans (BPair.norm_oneValue _)
        (BPair.oneValue_symm
          (ground.swap_congr (BPair.norm_oneValue _))),
     scaleP_neg c p⟩

/-- A coefficient family against a polynomial family: each
coefficient rescales its own polynomial and the rescalings sum,
the walk stopping at whichever family runs out. -/
def scaleDot : List BPair → List Poly → Poly
  | [], _ => []
  | _ :: _, [] => []
  | c :: cs, p :: ps => add (scaleP c p) (scaleDot cs ps)

/-- A coefficient fold's count sits at the polynomial family's
shared bound: every entry of the family within a count puts the
fold there too. -/
theorem scaleDot_len_le : ∀ (r : List BPair) (u : List Poly) {k : Nat},
    (∀ j, j < u.length →
      (ground.getAt ([] : Poly) u j).length ≤ k) →
    (scaleDot r u).length ≤ k
  | [], _, _, _ => Nat.zero_le _
  | _ :: _, [], _, _ => Nat.zero_le _
  | c :: cs, p :: ps, k, h => by
    show (add (scaleP c p) (scaleDot cs ps)).length ≤ k
    refine add_len_le _ _ _ ?_ (scaleDot_len_le cs ps
      (fun j hj => h (j + 1) (Nat.succ_le_succ hj)))
    show (p.map _).length ≤ k
    rw [ground.length_map]
    exact h 0 (Nat.succ_le_succ (Nat.zero_le _))

/-- The coefficient fold against a polynomial family reads its own
index fold over the key range, one scaled member per key. -/
theorem scaleDot_getAt : ∀ (r : List BPair) (u : List Poly),
    r.length = u.length →
    scaleDot r u
      = ground.famFold add []
          (fun j => scaleP (ground.getAt BPair.unit r j)
            (ground.getAt ([] : Poly) u j)) (List.range r.length)
  | [], [], _ => rfl
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | c :: r, p :: u, h => by
    show add (scaleP c p) (scaleDot r u)
      = ground.famFold add []
          (fun j => scaleP (ground.getAt BPair.unit (c :: r) j)
            (ground.getAt ([] : Poly) (p :: u) j))
          (List.range (r.length + 1))
    rw [ground.famFold_range_cons add ([] : Poly)
      (fun j => scaleP (ground.getAt BPair.unit (c :: r) j)
        (ground.getAt ([] : Poly) (p :: u) j)) r.length]
    exact congrArg (fun z => add (scaleP c p) z)
      (scaleDot_getAt r u (Nat.succ.inj h))

/-- The memberwise swap's key read is the key's own swap. -/
theorem getAt_neg : ∀ (l : Poly) (k : Nat),
    getAt BPair.unit (neg l) k = (getAt BPair.unit l k).swap
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, k + 1 => getAt_neg l k

/-- The memberwise swap keeps the width. -/
theorem length_neg (p : Poly) : (neg p).length = p.length :=
  ground.length_map BPair.swap p

/-- The memberwise swap is an involution, the balance carrier's own
`BPair.swap_swap` read entry by entry. -/
theorem neg_neg : ∀ p : Poly, neg (neg p) = p
  | [] => rfl
  | c :: p => by
    show c.swap.swap :: neg (neg p) = c :: p
    rw [neg_neg p, BPair.swap_swap c]

/-- The memberwise swap keeps a unit tail, entry by entry. -/
theorem unitTail_swapMap : ∀ q : Poly, unitTail q →
    unitTail (q.map BPair.swap)
  | [], _ => trivial
  | _ :: q, h => ⟨ground.swap_congr h.1, unitTail_swapMap q h.2⟩

/-- The memberwise swap respects the one-value class, entry by
entry, the two lists' lengths free. -/
theorem swapMap_oneValue : ∀ {r s : Poly}, oneValue r s →
    oneValue (r.map BPair.swap) (s.map BPair.swap)
  | [], s, h => unitTail_swapMap s h
  | _ :: r, [], h =>
    ⟨ground.swap_congr h.1, unitTail_swapMap r h.2⟩
  | _ :: _, _ :: _, h =>
    ⟨ground.swap_congr h.1, swapMap_oneValue h.2⟩

theorem neg_sum : ∀ p q : Poly, neg (add p q) = add (neg p) (neg q)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | c :: p, d :: q => by
    show (c + d).swap :: neg (add p q)
      = (c.swap + d.swap) :: add (neg p) (neg q)
    rw [neg_sum p q]
    rfl

private theorem neg_scale (c : BPair) : ∀ l : Poly,
    neg (l.map (fun d => c * d)) = (neg l).map (fun d => c * d)
  | [] => rfl
  | a :: l => by
    show (c * a).swap :: neg (l.map (fun d => c * d))
      = c * a.swap :: (neg l).map (fun d => c * d)
    rw [neg_scale c l]
    rfl

theorem neg_prod : ∀ (p q : Poly), neg (mul p q) = mul p (neg q)
  | [], _ => rfl
  | c :: p, q => by
    show neg (add (q.map (fun d => c * d)) (BPair.unit :: mul p q))
      = add ((neg q).map (fun d => c * d)) (BPair.unit :: mul p (neg q))
    rw [neg_sum (q.map (fun d => c * d)) (BPair.unit :: mul p q)]
    show add (neg (q.map (fun d => c * d))) (BPair.unit :: neg (mul p q))
      = add ((neg q).map (fun d => c * d)) (BPair.unit :: mul p (neg q))
    rw [neg_scale c q, neg_prod p q]

/-- The difference of two lists at one value reads the unit tail,
the one-value read's own witness at the swap join. -/
theorem diff_unitTail {p q : Poly} (h : oneValue p q) :
    unitTail (add p (neg q)) :=
  unitTail_of_getAt (fun k => by
    have h0 := getAt_add p (neg q) k
    rw [getAt_neg q k] at h0
    exact BPair.oneValue_trans h0 (ground.unitOfOne (oneValue_getAt k h)))

theorem ov_of_diff {p q : Poly} (h : unitTail (add p (neg q))) :
    oneValue p q :=
  ov_of_getAt (fun k => ground.oneOfUnit (by
    have h0 : (getAt BPair.unit p k + getAt BPair.unit (neg q) k).oneValue
        BPair.unit :=
      BPair.oneValue_trans (BPair.oneValue_symm (getAt_add p (neg q) k))
        (getAt_unitTail h k)
    rw [getAt_neg q k] at h0
    exact h0))

/-! The convolution's algebra at the reads it is consumed through. -/

theorem mul_nil : ∀ p : Poly, unitTail (mul p [])
  | [] => trivial
  | _ :: p => ⟨BPair.oneValue_refl _, mul_nil p⟩

private theorem unitTail_scale {a : BPair} (h : a.oneValue BPair.unit) :
    ∀ l : Poly, unitTail (l.map (fun d => a * d))
  | [] => trivial
  | c :: l => ⟨scale_unit h c, unitTail_scale h l⟩

private theorem scale_congr (c : BPair) {q q' : Poly} (h : oneValue q q') :
    oneValue (q.map (fun d => c * d)) (q'.map (fun d => c * d)) :=
  ov_of_getAt (fun k =>
    BPair.oneValue_trans (getAt_scale c q k)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl c) (oneValue_getAt k h))
        (BPair.oneValue_symm (getAt_scale c q' k))))

theorem mul_congr : ∀ (p : Poly) {q q' : Poly}, oneValue q q' →
    oneValue (mul p q) (mul p q')
  | [], _, _, _ => trivial
  | c :: p, _, _, h =>
    add_congr (scale_congr c h) ⟨BPair.oneValue_refl _, mul_congr p h⟩

private theorem map_sum (c : BPair) : ∀ q r : Poly,
    (add q r).map (fun d => c * d)
      = add (q.map (fun d => c * d)) (r.map (fun d => c * d))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: q, b :: r => by
    show c * (a + b) :: (add q r).map (fun d => c * d)
      = (c * a + c * b) :: add (q.map (fun d => c * d))
          (r.map (fun d => c * d))
    rw [BPair.left_distrib, map_sum c q r]

private theorem cons_ov {c d : BPair} (h1 : c.oneValue d) {p q : Poly}
    (h2 : oneValue p q) : oneValue (c :: p) (d :: q) := ⟨h1, h2⟩

theorem cons_unit_add (x y : Poly) :
    oneValue (BPair.unit :: add x y) (add (BPair.unit :: x) (BPair.unit :: y)) :=
  ⟨BPair.oneValue_symm (BPair.add_unit BPair.unit), oneValue_refl _⟩

theorem mul_sum : ∀ (p q r : Poly),
    oneValue (mul p (add q r)) (add (mul p q) (mul p r))
  | [], _, _ => trivial
  | c :: p, q, r => by
    show oneValue
      (add ((add q r).map (fun d => c * d)) (BPair.unit :: mul p (add q r)))
      (add (add (q.map (fun d => c * d)) (BPair.unit :: mul p q))
        (add (r.map (fun d => c * d)) (BPair.unit :: mul p r)))
    rw [map_sum c q r]
    exact oneValue_trans
      (add_congr (oneValue_refl _)
        (oneValue_trans
          (cons_ov (BPair.oneValue_refl BPair.unit) (mul_sum p q r))
          (cons_unit_add (mul p q) (mul p r))))
      (add_shuffle _ _ _ _)

theorem mul_single : ∀ (p : Poly) (a : BPair),
    oneValue (mul p [a]) (p.map (fun d => a * d))
  | [], _ => trivial
  | c :: p, a =>
    ⟨BPair.oneValue_trans (BPair.add_unit (c * a))
      (BPair.oneValue_of_eq (BPair.mul_comm c a)), mul_single p a⟩

private theorem map_shift (c : BPair) : ∀ (n : Nat) (q : Poly),
    oneValue ((shiftUp n q).map (fun d => c * d))
      (shiftUp n (q.map (fun d => c * d)))
  | 0, _ => oneValue_refl _
  | n + 1, q => ⟨BPair.mul_unit c, map_shift c n q⟩

/-- The key shift passes the product on its factor. -/
theorem mul_shiftUp : ∀ (p : Poly) (n : Nat) (q : Poly),
    oneValue (mul p (shiftUp n q)) (shiftUp n (mul p q))
  | [], n, _ => unitTail_shiftUp n trivial
  | c :: p, n, q => by
    show oneValue
      (add ((shiftUp n q).map (fun d => c * d))
        (BPair.unit :: mul p (shiftUp n q)))
      (shiftUp n (add (q.map (fun d => c * d)) (BPair.unit :: mul p q)))
    refine oneValue_trans (add_congr (map_shift c n q)
      (?_ : oneValue (BPair.unit :: mul p (shiftUp n q))
        (shiftUp n (BPair.unit :: mul p q)))) (oneValue_symm (shiftUp_add n _ _))
    rw [shift_cons n (mul p q)]
    exact ⟨BPair.oneValue_refl _, mul_shiftUp p n q⟩

private theorem mul_snoc (p q : Poly) (a : BPair) :
    oneValue (mul p (q ++ [a]))
      (add (mul p q) (shiftUp q.length (p.map (fun d => a * d)))) :=
  oneValue_trans (mul_congr p (append_add q [a]))
    (oneValue_trans (mul_sum p q (shiftUp q.length [a]))
      (add_congr (oneValue_refl _)
        (oneValue_trans (mul_shiftUp p q.length [a])
          (shiftUp_ov q.length (mul_single p a)))))

private theorem mul_len : ∀ (p q : Poly), 1 ≤ q.length → ∀ n : Nat,
    p.length + q.length ≤ n + 1 → (mul p q).length ≤ n
  | [], _, _, _, _ => Nat.zero_le _
  | c :: p, q, hq, n, h => by
    have h1 : q.length + 1 ≤ p.length + 1 + q.length := by
      rw [Nat.add_comm (p.length + 1) q.length]
      exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le _)) q.length
    have hqn : q.length ≤ n :=
      Nat.le_of_succ_le_succ (Nat.le_trans h1 h)
    refine add_len_le _ _ n (by rw [ground.length_map]; exact hqn) ?_
    cases n with
    | zero => exact absurd (Nat.le_trans hq hqn) (Nat.not_succ_le_zero 0)
    | succ m =>
      show (mul p q).length + 1 ≤ m + 1
      refine Nat.succ_le_succ (mul_len p q hq m ?_)
      have h2 : p.length + q.length + 1 ≤ m + 1 + 1 := by
        rw [Nat.add_right_comm p.length q.length 1]
        exact h
      exact Nat.le_of_succ_le_succ h2

private theorem unitTail_rev : ∀ {l : Poly}, unitTail l → unitTail l.reverse
  | [], _ => trivial
  | a :: l, h => by
    rw [ground.reverse_cons a l]
    exact unitTail_join (unitTail_rev h.2) ⟨h.1, trivial⟩

/-- The unit family at a stated count: every entry the sum's
unit, the replicate's fold. -/
theorem unitTail_replicate : ∀ n : Nat,
    unitTail (List.replicate n BPair.unit)
  | 0 => trivial
  | n + 1 => ⟨BPair.oneValue_refl _, unitTail_replicate n⟩

/-! The descent's own recursion, unfolded at its fuel. -/

private theorem nil_of_len : ∀ p : Poly, p.length ≤ 0 → p = []
  | [], _ => rfl
  | _ :: _, h => absurd h (Nat.not_succ_le_zero _)

private theorem sub_succ (a b : Nat) (h : b ≤ a) : a - b + 1 = a + 1 - b := by
  have e1 : b + (a - b + 1) = a + 1 := by
    rw [← Nat.add_assoc, ground.natAddSubCancel h]
  have e2 : b + (a + 1 - b) = a + 1 :=
    ground.natAddSubCancel (Nat.le_trans h (Nat.le_succ a))
  exact ground.addCancelL b (e1.trans e2.symm)

private theorem snoc_cases : ∀ p : Poly, p = [] ∨
    ∃ (q : Poly) (a : BPair), p = q ++ [a] ∧ q.length + 1 = p.length
  | [] => Or.inl rfl
  | a :: t => by
    cases snoc_cases t with
    | inl h => exact Or.inr ⟨[], a, by rw [h]; rfl, by rw [h]; rfl⟩
    | inr h =>
      obtain ⟨q, b, hq, hl⟩ := h
      exact Or.inr ⟨a :: q, b, by rw [hq]; rfl, by
        show q.length + 1 + 1 = t.length + 1
        rw [hl]⟩

private theorem subTop_len : ∀ (A B : List BPair),
    (subTop A B).length = A.length
  | [], [] => rfl
  | _ :: _, [] => rfl
  | [], _ :: _ => rfl
  | _ :: A, _ :: B => by
    show (subTop A B).length + 1 = A.length + 1
    rw [subTop_len A B]

private theorem divGo_succ (f : Nat) (stf ptf : List BPair) :
    divGo (f + 1) stf ptf =
      (if ptf.length ≤ stf.length then ([], padTo stf.length ptf)
        else match ptf with
          | [] => ([], padTo stf.length [])
          | c :: rest =>
            let s := divGo f stf (subTop rest (stf.map (fun d => c * d)))
            (c :: s.1, s.2)) := rfl

private theorem divGo_stop : ∀ (f : Nat) (stf ptf : List BPair),
    ptf.length ≤ stf.length → divGo f stf ptf = ([], padTo stf.length ptf)
  | 0, _, _, _ => rfl
  | _ + 1, stf, ptf, h => by rw [divGo_succ, if_pos h]

private theorem divGo_cons (f : Nat) (stf : List BPair) (c : BPair)
    (rest : List BPair) (h : ¬ ((c :: rest).length ≤ stf.length)) :
    divGo (f + 1) stf (c :: rest) =
      (c :: (divGo f stf (subTop rest (stf.map (fun d => c * d)))).1,
        (divGo f stf (subTop rest (stf.map (fun d => c * d)))).2) := by
  rw [divGo_succ, if_neg h]

private theorem div_stop (s P : Poly) (h : P.length ≤ s.length) :
    div s P = ([], (padTo s.length P.reverse).reverse) := by
  have e : divGo P.length s.reverse P.reverse
      = ([], padTo s.reverse.length P.reverse) :=
    divGo_stop P.length s.reverse P.reverse
      (by rw [ground.length_reverse P, ground.length_reverse s]; exact h)
  show ((divGo P.length s.reverse P.reverse).1.reverse,
      (divGo P.length s.reverse P.reverse).2.reverse) = _
  rw [e, ground.length_reverse s]
  rfl

private theorem div_snoc (s P' : Poly) (c : BPair) (h : s.length ≤ P'.length) :
    div s (P' ++ [c]) =
      ((div s ((subTop P'.reverse
          (s.reverse.map (fun d => c * d))).reverse)).1 ++ [c],
        (div s ((subTop P'.reverse
          (s.reverse.map (fun d => c * d))).reverse)).2) := by
  have hW : (subTop P'.reverse (s.reverse.map (fun d => c * d))).length
      = P'.length := by rw [subTop_len, ground.length_reverse]
  have hrev : (P' ++ [c]).reverse = c :: P'.reverse := by
    rw [ground.reverse_append P' [c]]; rfl
  have hlen : (P' ++ [c]).length = P'.length + 1 := by
    rw [ground.length_append]
    rfl
  have hne : ¬ (P'.reverse.length + 1 ≤ s.reverse.length) := by
    rw [ground.length_reverse P', ground.length_reverse s]
    exact fun hc => Nat.not_succ_le_self P'.length (Nat.le_trans hc h)
  have hd : div s ((subTop P'.reverse (s.reverse.map (fun d => c * d))).reverse)
      = ((divGo P'.length s.reverse
            (subTop P'.reverse (s.reverse.map (fun d => c * d)))).1.reverse,
          (divGo P'.length s.reverse
            (subTop P'.reverse (s.reverse.map (fun d => c * d)))).2.reverse) := by
    show ((divGo (subTop P'.reverse (s.reverse.map (fun d => c * d))).reverse.length
        s.reverse (subTop P'.reverse
          (s.reverse.map (fun d => c * d))).reverse.reverse).1.reverse,
      (divGo (subTop P'.reverse (s.reverse.map (fun d => c * d))).reverse.length
        s.reverse (subTop P'.reverse
          (s.reverse.map (fun d => c * d))).reverse.reverse).2.reverse) = _
    rw [ground.reverse_reverse, ground.length_reverse, hW]
  show ((divGo (P' ++ [c]).length s.reverse (P' ++ [c]).reverse).1.reverse,
      (divGo (P' ++ [c]).length s.reverse (P' ++ [c]).reverse).2.reverse) = _
  rw [hrev, hlen, divGo_cons P'.length s.reverse c P'.reverse hne, hd,
    ground.reverse_cons c (divGo P'.length s.reverse
      (subTop P'.reverse (s.reverse.map (fun d => c * d)))).1]

private theorem subTop_read : ∀ (A B : List BPair), B.length ≤ A.length →
    oneValue (add (subTop A B).reverse
      (shiftUp (A.length - B.length) B.reverse)) A.reverse
  | [], [], _ => trivial
  | a :: A, [], _ => by
    exact add_unitTail ((a :: A).reverse) (unitTail_shiftUp _ trivial)
  | [], _ :: _, h => absurd h (Nat.not_succ_le_zero _)
  | r :: A, d :: B, h => by
    have hB : B.length ≤ A.length := Nat.le_of_succ_le_succ h
    have hlenA : (subTop A B).reverse.length = A.length := by
      rw [ground.length_reverse, subTop_len]
    have hlenB : (shiftUp (A.length - B.length) B.reverse).length = A.length := by
      rw [len_shift, ground.length_reverse, ground.subAdd hB]
    show oneValue (add ((r + d.swap) :: subTop A B).reverse
      (shiftUp (A.length + 1 - (B.length + 1)) (d :: B).reverse))
      (r :: A).reverse
    rw [ground.reverse_cons (r + d.swap) (subTop A B),
      ground.reverse_cons d B, ground.reverse_cons r A,
      Nat.succ_sub_succ A.length B.length,
      shift_append (A.length - B.length) B.reverse [d],
      add_split ((subTop A B).reverse) (shiftUp (A.length - B.length) B.reverse)
        (hlenA.trans hlenB.symm) [r + d.swap] [d]]
    exact ov_split
      (by rw [add_len _ _ (hlenA.trans hlenB.symm), hlenA,
        ground.length_reverse])
      (subTop_read A B hB) ⟨BPair.add_swap_self r d, trivial⟩

/-! The naming identity at the descent's output, and the cancellation
at the monic top. -/

private theorem div_read_stop (s P : Poly) (h : P.length ≤ s.length) :
    oneValue (add (mul (monic s) (div s P).1) (div s P).2) P
      ∧ (div s P).1.length = P.length - s.length
      ∧ (div s P).2.length = s.length := by
  have hpad : (padTo s.length P.reverse).reverse
      = P ++ (List.replicate (s.length - P.length) BPair.unit).reverse := by
    show (List.replicate (s.length - P.reverse.length) BPair.unit
      ++ P.reverse).reverse = _
    rw [ground.reverse_append, ground.reverse_reverse, ground.length_reverse]
  rw [div_stop s P h, hpad]
  refine ⟨?_, (ground.subLe P.length s.length h).symm, ?_⟩
  · exact oneValue_trans (unitTail_add (mul_nil (monic s)) _)
      (append_unit P (unitTail_rev (unitTail_replicate _)))
  · rw [ground.length_append, ground.length_reverse, ground.length_replicate,
      ground.natAddSubCancel h]

private theorem monic_len (s : Poly) : (monic s).length = s.length + 1 := by
  show (s ++ [BPair.ofPos Pos.one]).length = s.length + 1
  rw [ground.length_append]
  rfl

private theorem div_step (s P' P₁ Q₁ R₁ : Poly) (c : BPair)
    (hlen : P₁.length = P'.length) (hd : s.length ≤ P'.length)
    (hq : oneValue (add (mul (monic s) Q₁) R₁) P₁)
    (hql : Q₁.length = P'.length - s.length)
    (hsr : oneValue (add P₁ (shiftUp Q₁.length (s.map (fun d => c * d)))) P') :
    oneValue (add (mul (monic s) (Q₁ ++ [c])) R₁) (P' ++ [c]) := by
  have hY : (shiftUp Q₁.length (s.map (fun d => c * d))).length = P'.length := by
    rw [len_shift, ground.length_map, hql, ground.subAdd hd]
  have step1 : oneValue (mul (monic s) (Q₁ ++ [c]))
      (add (mul (monic s) Q₁)
        (shiftUp Q₁.length (s.map (fun d => c * d))
          ++ [c * BPair.ofPos Pos.one])) := by
    refine oneValue_trans (mul_snoc (monic s) Q₁ c) ?_
    show oneValue (add (mul (monic s) Q₁)
      (shiftUp Q₁.length ((s ++ [BPair.ofPos Pos.one]).map (fun d => c * d)))) _
    have hm : ([BPair.ofPos Pos.one] : Poly).map (fun d => c * d)
        = [c * BPair.ofPos Pos.one] := rfl
    rw [ground.map_append (fun d => c * d) s [BPair.ofPos Pos.one], hm,
      shift_append Q₁.length (s.map (fun d => c * d)) [c * BPair.ofPos Pos.one]]
    exact oneValue_refl _
  refine oneValue_trans (add_congr step1 (oneValue_refl R₁)) ?_
  refine oneValue_trans (add_swap3 (mul (monic s) Q₁)
    (shiftUp Q₁.length (s.map (fun d => c * d)) ++ [c * BPair.ofPos Pos.one])
    R₁) ?_
  refine oneValue_trans (add_congr hq (oneValue_refl _)) ?_
  rw [add_snoc P₁ (shiftUp Q₁.length (s.map (fun d => c * d)))
    (hlen.trans hY.symm) (c * BPair.ofPos Pos.one)]
  exact ov_split (by rw [add_len _ _ (hlen.trans hY.symm), hlen]) hsr
    ⟨ground.BPair.mul_one_read c, trivial⟩

private theorem div_read : ∀ (n : Nat) (s P : Poly), P.length ≤ n →
    oneValue (add (mul (monic s) (div s P).1) (div s P).2) P
      ∧ (div s P).1.length = P.length - s.length
      ∧ (div s P).2.length = s.length
  | 0, s, P, h => div_read_stop s P (Nat.le_trans h (Nat.zero_le _))
  | n + 1, s, P, h => by
    by_cases hle : P.length ≤ s.length
    · exact div_read_stop s P hle
    · obtain hnil | ⟨P', c, hPc, hPl⟩ := snoc_cases P
      · exact absurd (by rw [hnil]; exact Nat.zero_le _) hle
      · subst hPc
        have hsP' : s.length ≤ P'.length := by
          have hlt := Nat.lt_of_not_le hle
          rw [← hPl] at hlt
          exact Nat.le_of_lt_succ hlt
        have hfuel : P'.length ≤ n := by
          have hn : (P' ++ [c]).length ≤ n + 1 := h
          rw [← hPl] at hn
          exact Nat.le_of_succ_le_succ hn
        have hW : (subTop P'.reverse
            (s.reverse.map (fun d => c * d))).reverse.length = P'.length := by
          rw [ground.length_reverse, subTop_len, ground.length_reverse]
        obtain ⟨hq, hql, hrl⟩ := div_read n s
          ((subTop P'.reverse (s.reverse.map (fun d => c * d))).reverse)
          (by rw [hW]; exact hfuel)
        have hk : (div s ((subTop P'.reverse
            (s.reverse.map (fun d => c * d))).reverse)).1.length
            = P'.length - s.length := by rw [hql, hW]
        have hsr : oneValue (add (subTop P'.reverse
            (s.reverse.map (fun d => c * d))).reverse
            (shiftUp (div s ((subTop P'.reverse
              (s.reverse.map (fun d => c * d))).reverse)).1.length
              (s.map (fun d => c * d)))) P' := by
          have hb : (s.reverse.map (fun d => c * d)).length
              ≤ P'.reverse.length := by
            rw [ground.length_map, ground.length_reverse,
              ground.length_reverse]
            exact hsP'
          have hr := subTop_read P'.reverse (s.reverse.map (fun d => c * d)) hb
          rw [ground.reverse_reverse P', ground.length_reverse P',
            ground.length_map, ground.length_reverse s,
            ground.map_reverse (fun d => c * d) s.reverse,
            ground.reverse_reverse s] at hr
          rw [hk]
          exact hr
        rw [div_snoc s P' c hsP']
        refine ⟨div_step s P' _ _ _ c hW hsP' hq hk hsr, ?_, hrl⟩
        have hone : ([c] : Poly).length = 1 := rfl
        rw [ground.length_append, ground.length_append, hone, hk,
          sub_succ P'.length s.length hsP']

/-- The naming identity `P = S Q + R` at the division's output, the
descent's own read at every polynomial. -/
theorem div_identity (s P : Poly) :
    oneValue (add (mul (monic s) (div s P).1) (div s P).2) P :=
  (div_read P.length s P (Nat.le_refl _)).1

/-- The remainder's carrier sits at the divisor's below-top length. -/
theorem div_len (s P : Poly) : (div s P).2.length = s.length :=
  (div_read P.length s P (Nat.le_refl _)).2.2

private theorem mul_top : ∀ (p q : Poly) (n : Nat),
    p.length + q.length ≤ n + 1 → ∀ k : Nat, n ≤ k →
    (getAt BPair.unit (mul p q) k).oneValue BPair.unit
  | p, [], _, _, k, _ => getAt_unitTail (mul_nil p) k
  | p, b :: q, n, h, k, hk => by
    rw [getAt_over BPair.unit (mul p (b :: q)) k
      (Nat.le_trans (mul_len p (b :: q)
        (Nat.succ_le_succ (Nat.zero_le _)) n h) hk)]
    exact BPair.oneValue_refl _

private theorem shift_top (N : Nat) (X Z R : Poly)
    (hX : ∀ k : Nat, N ≤ k → (getAt BPair.unit X k).oneValue BPair.unit)
    (hR : ∀ k : Nat, N ≤ k → (getAt BPair.unit R k).oneValue BPair.unit)
    (h : oneValue (add X (shiftUp N Z)) R) : unitTail Z ∧ oneValue X R := by
  constructor
  · refine unitTail_of_getAt (fun j => ?_)
    have e1 := getAt_add X (shiftUp N Z) (N + j)
    rw [getAt_shiftUp_add N Z j] at e1
    have e3 : (getAt BPair.unit X (N + j) + getAt BPair.unit Z j).oneValue
        BPair.unit :=
      BPair.oneValue_trans (BPair.oneValue_symm e1)
        (BPair.oneValue_trans (oneValue_getAt (N + j) h)
          (hR (N + j) (Nat.le_add_right N j)))
    exact bp_cancel
      (BPair.oneValue_trans e3
        (BPair.oneValue_symm (BPair.add_unit BPair.unit)))
      (hX (N + j) (Nat.le_add_right N j))
  · refine ov_of_getAt (fun k => ?_)
    cases Nat.lt_or_ge k N with
    | inl hlt =>
      have e1 := getAt_add X (shiftUp N Z) k
      rw [getAt_shiftUp_lt N Z k hlt] at e1
      exact BPair.oneValue_trans
        (BPair.oneValue_symm (BPair.add_unit (getAt BPair.unit X k)))
        (BPair.oneValue_trans (BPair.oneValue_symm e1) (oneValue_getAt k h))
    | inr hge =>
      exact BPair.oneValue_trans (hX k hge) (BPair.oneValue_symm (hR k hge))

theorem monic_cancel : ∀ (n : Nat) (s Q R : Poly), Q.length ≤ n →
    R.length ≤ s.length → oneValue (mul (monic s) Q) R → unitTail Q
  | 0, _, Q, _, hn, _, _ => by rw [nil_of_len Q hn]; exact trivial
  | n + 1, s, Q, R, hn, hR, h => by
    obtain hnil | ⟨Q', a, hQa, hQl⟩ := snoc_cases Q
    · rw [hnil]; exact trivial
    · subst hQa
      have hfuel : Q'.length ≤ n := by
        have hn' : (Q' ++ [a]).length ≤ n + 1 := hn
        rw [← hQl] at hn'
        exact Nat.le_of_succ_le_succ hn'
      have hYlen : (shiftUp Q'.length (s.map (fun d => a * d))).length
          = Q'.length + s.length := by rw [len_shift, ground.length_map]
      have h1 : oneValue (mul (monic s) (Q' ++ [a]))
          (add (add (mul (monic s) Q')
            (shiftUp Q'.length (s.map (fun d => a * d))))
            (shiftUp (Q'.length + s.length) [a * BPair.ofPos Pos.one])) := by
        refine oneValue_trans (mul_snoc (monic s) Q' a) ?_
        show oneValue (add (mul (monic s) Q')
          (shiftUp Q'.length ((s ++ [BPair.ofPos Pos.one]).map
            (fun d => a * d)))) _
        have hm : ([BPair.ofPos Pos.one] : Poly).map (fun d => a * d)
            = [a * BPair.ofPos Pos.one] := rfl
        rw [ground.map_append (fun d => a * d) s [BPair.ofPos Pos.one], hm,
          shift_append Q'.length (s.map (fun d => a * d))
            [a * BPair.ofPos Pos.one]]
        refine oneValue_trans (add_congr (oneValue_refl _)
          (append_add (shiftUp Q'.length (s.map (fun d => a * d)))
            [a * BPair.ofPos Pos.one])) ?_
        rw [hYlen]
        exact add_join _ _ _
      obtain ⟨hz, hXR⟩ := shift_top (Q'.length + s.length)
        (add (mul (monic s) Q') (shiftUp Q'.length (s.map (fun d => a * d))))
        [a * BPair.ofPos Pos.one] R
        (fun k hk => BPair.oneValue_trans (getAt_add _ _ k)
          (BPair.oneValue_trans
            (BPair.add_congr
              (mul_top (monic s) Q' (Q'.length + s.length)
                (by
                  rw [monic_len s, Nat.add_right_comm s.length 1
                    Q'.length, Nat.add_comm s.length Q'.length]
                  exact Nat.le_refl _) k hk)
              (BPair.oneValue_of_eq
                (getAt_over BPair.unit _ k (by rw [hYlen]; exact hk))))
            (BPair.add_unit BPair.unit)))
        (fun k hk => BPair.oneValue_of_eq (getAt_over BPair.unit R k
          (Nat.le_trans hR (Nat.le_trans (Nat.le_add_left s.length Q'.length) hk))))
        (oneValue_trans (oneValue_symm h1) h)
      have ha : a.oneValue BPair.unit :=
        BPair.oneValue_trans (BPair.oneValue_symm (ground.BPair.mul_one_read a)) hz.1
      exact unitTail_join
        (monic_cancel n s Q' R hfuel hR
          (oneValue_trans (oneValue_symm
            (add_unitTail (mul (monic s) Q')
              (unitTail_shiftUp Q'.length (unitTail_scale ha s)))) hXR))
        ⟨ha, trivial⟩

/-- The pair `(Q, R)` is one value by the descent at the monic top:
every solution with remainder below the top reads the descent's
output, the difference argument at the monic top — the top term of
`S (Q − Q₀)` sits above the remainders' keys, so the quotients agree
and the remainders with them. -/
theorem div_unique (s P : Poly) : ∀ Q R, R.length = s.length →
    oneValue (add (mul (monic s) Q) R) P →
    oneValue Q (div s P).1 ∧ oneValue R (div s P).2 := by
  intro Q R hR h
  obtain ⟨hd, _, hr0⟩ := div_read P.length s P (Nat.le_refl _)
  have h3 : oneValue (add (mul (monic s) Q) R)
      (add (mul (monic s) (div s P).1) (div s P).2) :=
    oneValue_trans h (oneValue_symm hd)
  have hu : unitTail (add (add (mul (monic s) Q) R)
      (neg (add (mul (monic s) (div s P).1) (div s P).2))) := diff_unitTail h3
  rw [neg_sum, neg_prod] at hu
  have hu3 : unitTail (add (mul (monic s) (add Q (neg (div s P).1)))
      (add R (neg (div s P).2))) :=
    unitTail_oneValue_right
      (unitTail_oneValue_right hu (add_shuffle _ _ _ _))
      (add_congr (oneValue_symm (mul_sum (monic s) Q (neg (div s P).1)))
        (oneValue_refl _))
  have hlR : R.length = (neg (div s P).2).length := by
    rw [length_neg, hr0, hR]
  have hDR : (add R (neg (div s P).2)).length = s.length := by
    rw [add_len R (neg (div s P).2) hlR, hR]
  have hcanc : oneValue (mul (monic s) (add Q (neg (div s P).1)))
      (neg (add R (neg (div s P).2))) := by
    apply ov_of_diff
    rw [neg_neg]
    exact hu3
  have hQ : unitTail (add Q (neg (div s P).1)) :=
    monic_cancel (add Q (neg (div s P).1)).length s _ _ (Nat.le_refl _)
      (by rw [length_neg, hDR]; exact Nat.le_refl _) hcanc
  exact ⟨ov_of_diff hQ, add_cancel h3 (mul_congr (monic s) (ov_of_diff hQ))⟩

/-- A root is a value at which the linear factor's remainder — the
Horner read — has its two members equal. -/
def isRoot (P : Poly) (r : BPair) : Prop :=
  (eval P r).oneValue BPair.unit

instance (P : Poly) (r : BPair) : Decidable (isRoot P r) :=
  inferInstanceAs (Decidable (BPair.oneValue _ _))

/-- At a linear factor `⟨z : r⟩` the remainder is the Horner read
at `r`. -/
def hornerRead (P : Poly) (r : BPair) : Prop :=
  oneValue (div [r.swap] P).2 [eval P r]

instance (P : Poly) (r : BPair) : Decidable (hornerRead P r) :=
  decOneValue _ _

/-- The cleared evaluation's walk along the coefficient list: the
accumulated value `S`, the point's running power `pw` and the
clearing's remaining count `r` advance together, a key with a
clearing still owed charging the accumulator with one clearing
before the key's coefficient enters against the running power, and
the exhausted list paying the clearing that remains.  This is the
computing read; a display reads the collection (`evalClear_read`). -/
private def evalClearGo (ln cB : BPair) :
    Poly → BPair → BPair → Nat → BPair
  | [], S, _, r => (S * ground.bpow cB r).norm
  | a :: t, S, pw, 0 =>
    evalClearGo ln cB t (S + a * pw).norm (pw * ln).norm 0
  | a :: t, S, pw, r + 1 =>
    evalClearGo ln cB t (S * cB + a * pw).norm (pw * ln).norm r

/-- The cleared evaluation at a composite point `[ln : c]`:
`Σ_k p_k ln^k c^(K-k)`, the Horner read's value rescaled by the
clearing's stated power, the homogeneity principle's spelling; the
read is faithful exactly where `K` bounds every key.  The walk
enters at the unit accumulator, the point's nought power and the
clearing's count one beyond the stated power, the constant key's
own step spending that one against the unit. -/
def evalClear (p : Poly) (ln : BPair) (c : Pos) (K : Nat) : BPair :=
  match p with
  | [] => BPair.unit
  | _ :: _ =>
    evalClearGo ln (BPair.ofPos c) p BPair.unit (BPair.ofPos Pos.one)
      (K + 1)

/-- The vacant list's cleared evaluation reads the sum's unit. -/
theorem evalClear_nil (ln : BPair) (c : Pos) (K : Nat) :
    evalClear [] ln c K = BPair.unit := rfl

/-- The running power's step: the advanced power against the
point's power at a key is the point's power at the key beyond. -/
private theorem powStep (ln pw : BPair) (j : Nat) :
    ((pw * ln).norm * ground.bpow ln j).oneValue
      (pw * ground.bpow ln (j + 1)) :=
  BPair.oneValue_trans
    (BPair.mul_congr_left (BPair.norm_oneValue (pw * ln)))
    (BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc pw ln (ground.bpow ln j)))
      (BPair.mul_congr (BPair.oneValue_refl pw)
        (BPair.oneValue_symm
          (BPair.norm_oneValue (ln * ground.bpow ln j)))))

/-- The walk's read: the accumulated value at the clearing's
remaining count joined to the coefficients' fold, each key against
the running power at its own key and the clearing at the count
below the remainder. -/
private theorem evalClearGo_read (ln cB : BPair) :
    ∀ (t : Poly) (S pw : BPair) (r : Nat),
    (evalClearGo ln cB t S pw r).oneValue
      (S * ground.bpow cB r
        + ground.famFold BPair.add BPair.unit
            (fun j => ground.getAt BPair.unit t j
              * (pw * ground.bpow ln j)
              * ground.bpow cB (r - 1 - j))
            (List.range t.length))
  | [], _, _, _ =>
    BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_symm (BPair.add_unit _))
  | a :: t, S, pw, 0 => by
    have hze : ∀ j : Nat, 0 - 1 - j = 0 - 1 - (j + 1) := fun j => by
      rw [ground.subSub 0 1 j, ground.subSub 0 1 (j + 1),
        Nat.zero_sub (1 + j), Nat.zero_sub (1 + (j + 1))]
    rw [show (a :: t).length = t.length + 1 from rfl,
      ground.foldB_range_cons]
    refine BPair.oneValue_trans
      (evalClearGo_read ln cB t (S + a * pw).norm (pw * ln).norm 0) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.mul_congr_left (BPair.norm_oneValue (S + a * pw)))
        (ground.famFold_congr_members_ov BPair.oneValue BPair.add
          BPair.unit BPair.oneValue_refl BPair.add_congr
          (fun j => ground.getAt BPair.unit t j
            * ((pw * ln).norm * ground.bpow ln j)
            * ground.bpow cB (0 - 1 - j))
          (fun j => ground.getAt BPair.unit (a :: t) (j + 1)
            * (pw * ground.bpow ln (j + 1))
            * ground.bpow cB (0 - 1 - (j + 1)))
          (List.range t.length)
          (fun j _ =>
            BPair.mul_congr
              (BPair.mul_congr (BPair.oneValue_refl _) (powStep ln pw j))
              (BPair.oneValue_of_eq
                (congrArg (ground.bpow cB) (hze j)))))) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_of_eq
          (BPair.right_distrib S (a * pw) (ground.bpow cB 0)))
        (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_assoc _ _ _)) ?_
    exact BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr
        (BPair.mul_congr_left
          (BPair.mul_congr (BPair.oneValue_refl a)
            (BPair.oneValue_symm (BPair.mul_one_read pw))))
        (BPair.oneValue_refl _))
  | a :: t, S, pw, r + 1 => by
    have hze : ∀ j : Nat, r - 1 - j = r + 1 - 1 - (j + 1) := fun j => by
      rw [ground.subSub r 1 j, Nat.add_comm 1 j,
        show r + 1 - 1 = r from rfl]
    have hS : (S * cB * ground.bpow cB r).oneValue
        (S * ground.bpow cB (r + 1)) :=
      BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_assoc S cB (ground.bpow cB r)))
        (BPair.mul_congr (BPair.oneValue_refl S)
          (BPair.oneValue_symm
            (BPair.norm_oneValue (cB * ground.bpow cB r))))
    rw [show (a :: t).length = t.length + 1 from rfl,
      ground.foldB_range_cons]
    refine BPair.oneValue_trans
      (evalClearGo_read ln cB t (S * cB + a * pw).norm (pw * ln).norm r)
      ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.mul_congr_left (BPair.norm_oneValue (S * cB + a * pw)))
        (ground.famFold_congr_members_ov BPair.oneValue BPair.add
          BPair.unit BPair.oneValue_refl BPair.add_congr
          (fun j => ground.getAt BPair.unit t j
            * ((pw * ln).norm * ground.bpow ln j)
            * ground.bpow cB (r - 1 - j))
          (fun j => ground.getAt BPair.unit (a :: t) (j + 1)
            * (pw * ground.bpow ln (j + 1))
            * ground.bpow cB (r + 1 - 1 - (j + 1)))
          (List.range t.length)
          (fun j _ =>
            BPair.mul_congr
              (BPair.mul_congr (BPair.oneValue_refl _) (powStep ln pw j))
              (BPair.oneValue_of_eq
                (congrArg (ground.bpow cB) (hze j)))))) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_of_eq
          (BPair.right_distrib (S * cB) (a * pw) (ground.bpow cB r)))
        (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.add_congr hS (BPair.oneValue_refl _))
        (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_assoc _ _ _)) ?_
    exact BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr
        (BPair.mul_congr_left
          (BPair.mul_congr (BPair.oneValue_refl a)
            (BPair.oneValue_symm (BPair.mul_one_read pw))))
        (BPair.oneValue_refl _))

/-- The cleared evaluation at the sum's unit point keeps the
constant key alone at the clearing's stated power: every key beyond
the constant reads the unit's own power, the accumulating sum
stable there (`def:poly`'s evaluation at the homogeneity
principle's clearing). -/
theorem evalClear_unit (p : Poly) (c : Pos) (K : Nat) :
    (evalClear p BPair.unit c K).oneValue
      (ground.bpow (BPair.ofPos c) K
        * ground.getAt BPair.unit p 0) := by
  match p with
  | [] => exact BPair.oneValue_symm (BPair.mul_unit _)
  | q :: tl =>
    refine BPair.oneValue_trans
      (evalClearGo_read BPair.unit (BPair.ofPos c) (q :: tl)
        BPair.unit (BPair.ofPos Pos.one) (K + 1)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.unit_mul _) (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans (BPair.unit_add _) ?_
    refine ground.foldB_pick _ 0 _ (List.range (q :: tl).length)
      (ground.countOf_range_one (Nat.succ_pos tl.length)) ?_ ?_
    · exact BPair.oneValue_trans
        (BPair.mul_congr_left
          (BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl _)
              (BPair.mul_one_read (BPair.ofPos Pos.one)))
            (BPair.mul_one_read _)))
        (BPair.oneValue_of_eq (BPair.mul_comm _ _))
    · intro x _ hx
      match x with
      | 0 => exact absurd rfl hx
      | k + 1 =>
        exact BPair.oneValue_trans
          (BPair.mul_congr_left
            (BPair.oneValue_trans
              (BPair.mul_congr (BPair.oneValue_refl _)
                (BPair.oneValue_trans
                  (BPair.mul_congr (BPair.oneValue_refl _)
                    (ground.bpow_unit_succ k))
                  (BPair.mul_unit _)))
              (BPair.mul_unit _)))
          (BPair.unit_mul _)

/-! The convolution's own algebra at the one-value class.  The sum
adds componentwise and the product convolves (`def:poly`), so both
read the balance pairs' algebra one monomial key at a time: the sum
commutes and associates, the product distributes over either
factor's sum, a scale transports across it, and the product
commutes and associates.  The recursion `(c + zP)Q = cQ + z(PQ)` is
one-sided, so each read off it decomposes its second factor at the
monomial split `c :: P = ⟨c⟩ + z P` — the constant against the
shift — and closes on `mul_single` and `mul_shiftUp`.  The deck
families' doubling identity (`lem:fiberdec`'s display
`p_L = ⟨x:2⟩ P_L² + 2`) is the kit's consumer. -/

/-- The componentwise sum commutes. -/
theorem add_comm (p q : Poly) : oneValue (add p q) (add q p) :=
  ov_of_getAt (fun k =>
    BPair.oneValue_trans (getAt_add p q k)
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.add_comm _ _))
        (BPair.oneValue_symm (getAt_add q p k))))

/-- The four-term exchange: two joined sums re-pair at the crossed
members. -/
theorem add_add_comm (a b c d : List BPair) :
    poly.oneValue (poly.add (poly.add a b) (poly.add c d))
      (poly.add (poly.add a c) (poly.add b d)) :=
  poly.ov_of_getAt (fun k => by
    refine BPair.oneValue_trans (poly.getAt_add _ _ k) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (poly.getAt_add a b k) (poly.getAt_add c d k)) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (poly.getAt_add _ _ k) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (poly.getAt_add a c k) (poly.getAt_add b d k)) ?_
    refine BPair.oneValue_of_eq ?_
    rw [BPair.add_assoc, BPair.add_assoc,
      ← BPair.add_assoc (ground.getAt BPair.unit c k)
        (ground.getAt BPair.unit b k) (ground.getAt BPair.unit d k),
      BPair.add_comm (ground.getAt BPair.unit c k)
        (ground.getAt BPair.unit b k),
      BPair.add_assoc (ground.getAt BPair.unit b k)
        (ground.getAt BPair.unit c k) (ground.getAt BPair.unit d k)])

/-- The componentwise sum's left commutation, the two AC moves'
join. -/
theorem add_left_comm (a b c : Poly) :
    oneValue (add a (add b c)) (add b (add a c)) :=
  ov_of_getAt (fun k =>
    BPair.oneValue_trans (getAt_add a (add b c) k)
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) (getAt_add b c k))
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (BPair.add_left_comm _ _ _))
          (BPair.oneValue_trans
            (BPair.add_congr (BPair.oneValue_refl _)
              (BPair.oneValue_symm (getAt_add a c k)))
            (BPair.oneValue_symm (getAt_add b (add a c) k))))))

/-- A polynomial reading its own memberwise swap is a unit tail:
every key's coefficient reads its own swap there, so it sits at the
sum's unit (`BPair.unitOfSwap`). -/
theorem unitTail_of_negRead : ∀ {p : Poly},
    oneValue p (neg p) → unitTail p
  | [], _ => trivial
  | _ :: _, h => ⟨BPair.unitOfSwap h.1, unitTail_of_negRead h.2⟩

/-- A polynomial and its memberwise swap join to the sum's unit at
every key. -/
theorem add_neg : ∀ p : Poly, unitTail (add p (neg p))
  | [] => trivial
  | c :: p => ⟨BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_comm c c.swap))
      (BPair.swap_add_null (BPair.oneValue_refl c)),
    add_neg p⟩

/-- The unit scalar's scaling reads the list itself, entry by
entry. -/
theorem scale_one : ∀ q : Poly,
    oneValue (q.map (fun d => BPair.ofPos .one * d)) q
  | [] => trivial
  | c :: q => ⟨BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_comm (BPair.ofPos .one) c))
      (BPair.mul_ofNat_one c), scale_one q⟩

/-- The unit monomial's product is read off. -/
theorem one_mul (q : Poly) :
    oneValue (mul one q) q :=
  oneValue_trans
    (show oneValue (add (q.map (fun d => BPair.ofPos .one * d))
        [BPair.unit]) (q.map (fun d => BPair.ofPos .one * d)) from
      add_unitTail _ ⟨BPair.oneValue_refl _, trivial⟩)
    (scale_one q)

/-- The two pairs' sum scales a list as their two scalings' sum. -/
private theorem scale_add (c d : BPair) : ∀ l : Poly,
    l.map (fun x => (c + d) * x)
      = add (l.map (fun x => c * x)) (l.map (fun x => d * x))
  | [] => rfl
  | a :: l => by
    show (c + d) * a :: l.map (fun x => (c + d) * x)
      = (c * a + d * a) :: add (l.map (fun x => c * x))
          (l.map (fun x => d * x))
    rw [BPair.right_distrib, scale_add c d l]

/-- The product distributes over the left factor's sum, the
recursion's own read at the shared right factor. -/
theorem sum_mul : ∀ p q r : Poly,
    oneValue (mul (add p q) r) (add (mul p r) (mul q r))
  | [], _, _ => oneValue_refl _
  | c :: p, [], r => by
    show oneValue (mul (c :: p) r) (add (mul (c :: p) r) [])
    rw [add_nil]
    exact oneValue_refl _
  | c :: p, d :: q, r => by
    show oneValue
      (add (r.map (fun x => (c + d) * x)) (BPair.unit :: mul (add p q) r))
      (add (add (r.map (fun x => c * x)) (BPair.unit :: mul p r))
        (add (r.map (fun x => d * x)) (BPair.unit :: mul q r)))
    rw [scale_add c d r]
    exact oneValue_trans
      (add_congr (oneValue_refl _)
        (oneValue_trans
          (cons_ov (BPair.oneValue_refl BPair.unit) (sum_mul p q r))
          (cons_unit_add (mul p r) (mul q r))))
      (add_shuffle _ _ _ _)

/-- A scale on the left factor transports across the product. -/
theorem scale_mul (c : BPair) : ∀ q r : Poly,
    oneValue (mul (q.map (fun x => c * x)) r)
      ((mul q r).map (fun x => c * x))
  | [], _ => trivial
  | a :: q, r => by
    show oneValue
      (add (r.map (fun x => c * a * x))
        (BPair.unit :: mul (q.map (fun x => c * x)) r))
      ((add (r.map (fun x => a * x)) (BPair.unit :: mul q r)).map
        (fun x => c * x))
    rw [map_sum c (r.map (fun x => a * x)) (BPair.unit :: mul q r),
      ground.map_map (fun x => a * x) (fun x => c * x) r]
    exact add_congr
      (oneValue_map (fun x => c * a * x) (fun x => c * (a * x)) r (fun x _ => (fun x => BPair.oneValue_of_eq (BPair.mul_assoc c a x)) x))
      (cons_ov (BPair.oneValue_symm (BPair.mul_unit c))
        (scale_mul c q r))

/-- The monomial split of the recursion's second factor: the
product against `c :: P` reads the constant's scale with the
shifted product, the recursion's read on the other side. -/
private theorem mul_cons (q : Poly) (c : BPair) (p : Poly) :
    oneValue (mul q (c :: p))
      (add (q.map (fun x => c * x)) (BPair.unit :: mul q p)) :=
  oneValue_trans
    (mul_congr q
      (show oneValue (c :: p) (add [c] (BPair.unit :: p)) from
        ⟨BPair.oneValue_symm (BPair.add_unit c), oneValue_refl p⟩))
    (oneValue_trans (mul_sum q [c] (BPair.unit :: p))
      (add_congr (mul_single q c) (mul_shiftUp q 1 p)))

/-- The product commutes. -/
theorem mul_comm : ∀ p q : Poly, oneValue (mul p q) (mul q p)
  | [], q => mul_nil q
  | c :: p, q =>
    oneValue_symm (oneValue_trans (mul_cons q c p)
      (add_congr (oneValue_refl _)
        (cons_ov (BPair.oneValue_refl _)
          (oneValue_symm (mul_comm p q)))))

/-- The product associates. -/
theorem mul_assoc : ∀ p q r : Poly,
    oneValue (mul (mul p q) r) (mul p (mul q r))
  | [], _, _ => trivial
  | c :: p, q, r => by
    show oneValue (mul (add (q.map (fun x => c * x))
        (BPair.unit :: mul p q)) r)
      (add ((mul q r).map (fun x => c * x))
        (BPair.unit :: mul p (mul q r)))
    refine oneValue_trans (sum_mul _ _ r) (add_congr (scale_mul c q r) ?_)
    show oneValue (add (r.map (fun x => BPair.unit * x))
        (BPair.unit :: mul (mul p q) r))
      (BPair.unit :: mul p (mul q r))
    exact oneValue_trans
      (unitTail_add (unitTail_scale (BPair.oneValue_refl BPair.unit) r) _)
      (cons_ov (BPair.oneValue_refl _) (mul_assoc p q r))

/-- The product's congruence in its left factor, the commutation's
own read. -/
theorem mul_congr_left {p p' : Poly} (h : oneValue p p') (q : Poly) :
    oneValue (mul p q) (mul p' q) :=
  oneValue_trans (mul_comm p q)
    (oneValue_trans (mul_congr q h) (mul_comm q p'))

/-- A product reads one value against its factors' canonical
representatives. -/
theorem mul_vnorm_ov (p q : Poly) :
    oneValue (mul p q) (mul (vnorm p) (vnorm q)) :=
  oneValue_trans
    (mul_congr_left (oneValue_symm (vnorm_ov p)) q)
    (mul_congr (vnorm p) (oneValue_symm (vnorm_ov q)))

/-- The derivative from a successor key reads the derivative from the
key joined to the list itself, `(n+1+k) p_k = (n+k) p_k + p_k`. -/
theorem derivFrom_succ (n : Pos) : ∀ p : Poly,
    derivFrom (succ n) p = add (derivFrom n p) p
  | [] => rfl
  | x :: p => by
    show x.scale (succ n) :: derivFrom (succ (succ n)) p
      = (x.scale n + x) :: add (derivFrom (succ n) p) p
    have hh : x.scale (succ n) = x.scale n + x := by
      rw [← ground.add_one n, BPair.scale_addW, BPair.scale_one]
    rw [hh, derivFrom_succ (succ n) p]

/-- The derivative from the key one is the list joined to its own
derivative's shift: `(x P)' = P + x P'`. -/
theorem derivFrom_one (r : Poly) :
    oneValue (derivFrom .one r) (add r (BPair.unit :: deriv r)) := by
  match r with
  | [] => exact ⟨BPair.oneValue_refl _, trivial⟩
  | x :: t =>
    show oneValue (x.scale .one :: derivFrom (succ .one) t)
      ((x + BPair.unit) :: add t (derivFrom .one t))
    refine ⟨?_, ?_⟩
    · rw [BPair.scale_one]
      exact BPair.oneValue_symm (BPair.add_unit x)
    · rw [derivFrom_succ .one t]
      exact add_comm _ _

/-- The derivative passes a constant factor. -/
theorem derivFrom_map_mul (c : BPair) (n : Pos) : ∀ q : Poly,
    derivFrom n (q.map (fun x => c * x))
      = (derivFrom n q).map (fun x => c * x)
  | [] => rfl
  | x :: q => by
    show (c * x).scale n :: derivFrom (succ n) (q.map (fun x => c * x))
      = c * x.scale n :: (derivFrom (succ n) q).map (fun x => c * x)
    rw [derivFrom_map_mul c (succ n) q]
    have h : (c * x).scale n = c * x.scale n := by
      rw [← ground.one_mul n, BPair.scale_mul, BPair.scale_one,
        ground.one_mul]
    rw [h]

theorem deriv_map_mul (c : BPair) : ∀ q : Poly,
    deriv (q.map (fun x => c * x)) = (deriv q).map (fun x => c * x)
  | [] => rfl
  | _ :: q => derivFrom_map_mul c .one q

/-- The unit's multiples read the unit tail. -/
theorem unitTail_map_unit_mul : ∀ q : Poly,
    unitTail (q.map (fun x => BPair.unit * x))
  | [] => trivial
  | x :: q => ⟨BPair.unit_mul x, unitTail_map_unit_mul q⟩

/-- Four summands regroup, the first joining the third pair. -/
theorem add4_rearr (X A B C : Poly) :
    oneValue (add X (add A (add B C))) (add (add A B) (add X C)) :=
  ov_of_getAt (fun k => by
    refine BPair.oneValue_trans (getAt_add X _ k) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans (getAt_add A _ k)
          (BPair.add_congr (BPair.oneValue_refl _) (getAt_add B C k)))) ?_
    refine BPair.oneValue_trans ?_
      (BPair.oneValue_symm (BPair.oneValue_trans (getAt_add _ _ k)
        (BPair.add_congr (getAt_add A B k) (getAt_add X C k))))
    refine BPair.oneValue_of_eq ?_
    rw [← BPair.add_assoc, BPair.add_comm (getAt BPair.unit X k),
      BPair.add_assoc, BPair.add_assoc,
      ← BPair.add_assoc (getAt BPair.unit X k) (getAt BPair.unit B k),
      BPair.add_comm (getAt BPair.unit X k) (getAt BPair.unit B k),
      BPair.add_assoc (getAt BPair.unit B k)])

/-- The Leibniz read `(P Q)' = P' Q + P Q'`, one convolution
identity per key. -/
theorem deriv_mul : ∀ P Q : Poly,
    oneValue (deriv (mul P Q)) (add (mul (deriv P) Q) (mul P (deriv Q)))
  | [], _ => trivial
  | c :: p, q => by
    have hL : deriv (mul (c :: p) q)
        = add ((deriv q).map (fun x => c * x)) (derivFrom .one (mul p q)) := by
      show deriv (add (q.map (fun x => c * x)) (BPair.unit :: mul p q)) = _
      rw [deriv_add, deriv_map_mul]
      rfl
    rw [hL]
    -- the left side collected
    have h1 : oneValue (derivFrom .one (mul p q))
        (add (mul p q)
          (add (BPair.unit :: mul (deriv p) q)
            (BPair.unit :: mul p (deriv q)))) := by
      refine oneValue_trans (derivFrom_one (mul p q)) ?_
      refine add_congr (oneValue_refl _) ?_
      refine oneValue_trans (show oneValue (BPair.unit :: deriv (mul p q))
        (BPair.unit :: add (mul (deriv p) q) (mul p (deriv q))) from
        ⟨BPair.oneValue_refl _, deriv_mul p q⟩) ?_
      exact cons_unit_add _ _
    -- the right side collected
    have h2 : oneValue (mul (derivFrom .one p) q)
        (add (mul p q) (BPair.unit :: mul (deriv p) q)) := by
      refine oneValue_trans (mul_congr_left (derivFrom_one p) q) ?_
      refine oneValue_trans (mul_comm _ _) ?_
      refine oneValue_trans (mul_sum q _ _) ?_
      refine add_congr (mul_comm q p) ?_
      refine oneValue_trans (mul_comm q _) ?_
      show oneValue (add (q.map (fun x => BPair.unit * x))
        (BPair.unit :: mul (deriv p) q)) _
      exact unitTail_add (unitTail_map_unit_mul q) _
    have hLft : oneValue
        (add ((deriv q).map (fun x => c * x)) (derivFrom .one (mul p q)))
        (add ((deriv q).map (fun x => c * x))
          (add (mul p q)
            (add (BPair.unit :: mul (deriv p) q)
              (BPair.unit :: mul p (deriv q))))) :=
      add_congr (oneValue_refl _) h1
    have hR : oneValue
        (add (mul (derivFrom .one p) q)
          (add ((deriv q).map (fun x => c * x))
            (BPair.unit :: mul p (deriv q))))
        (add (add (mul p q) (BPair.unit :: mul (deriv p) q))
          (add ((deriv q).map (fun x => c * x))
            (BPair.unit :: mul p (deriv q)))) :=
      add_congr h2 (oneValue_refl _)
    exact oneValue_trans hLft
      (oneValue_trans (add4_rearr _ _ _ _) (oneValue_symm hR))

/-- The power's congruence in its base. -/
theorem powOf_congr {p q : Poly}
    (h : oneValue p q) : ∀ N : Nat,
    oneValue (powOf p N) (powOf q N)
  | 0 => oneValue_refl _
  | N + 1 =>
    oneValue_trans (mul_congr_left h (powOf p N))
      (mul_congr q (powOf_congr h N))

/-- The convolution's left commutation, the associativity against
the commutation. -/
theorem mul_left_comm (a b c : Poly) :
    oneValue (mul a (mul b c)) (mul b (mul a c)) :=
  oneValue_trans (oneValue_symm (mul_assoc a b c))
    (oneValue_trans (mul_congr_left (mul_comm a b) c)
      (mul_assoc b a c))

/-- The memberwise swap rides out of a product's left factor,
`neg_prod`'s read at the other side. -/
theorem neg_prod_left (A B : Poly) :
    oneValue (mul (neg A) B) (neg (mul A B)) := by
  refine oneValue_trans (mul_comm (neg A) B) ?_
  rw [← neg_prod B A]
  exact swapMap_oneValue (mul_comm B A)

/-- Two products exchange their inner factors. -/
theorem mul_exchange4 (a b c d : Poly) :
    oneValue (mul (mul a b) (mul c d))
      (mul (mul a c) (mul b d)) :=
  oneValue_trans (mul_assoc a b (mul c d))
    (oneValue_trans
      (mul_congr a
        (oneValue_trans
          (oneValue_symm (mul_assoc b c d))
          (oneValue_trans
            (mul_congr_left (mul_comm b c) d)
            (mul_assoc c b d))))
      (oneValue_symm (mul_assoc a c (mul b d))))

/-- The fold of a factor list at the product's unit. -/
def prodFold (ps : List Poly) : Poly :=
  ps.foldl mul one

/-- The product fold evaluates to the evaluations' fold. -/
theorem eval_prodFold (x : BPair) : ∀ (ps : List Poly) (acc : Poly),
    (eval (ps.foldl mul acc) x).oneValue
      (ps.foldl (fun a p => a * eval p x) (eval acc x))
  | [], _ => BPair.oneValue_refl _
  | p :: t, acc =>
    BPair.oneValue_trans (eval_prodFold x t (mul acc p))
      (ground.foldl_congr_seed BPair.oneValue
        (fun a p => a * eval p x)
        (fun _ h => BPair.mul_congr_left h) t (eval_mul acc p x))

/-- The fold of a family's factors at the product's unit. -/
def prodFoldMap {α : Type} (f : α → Poly) (l : List α) : Poly :=
  prodFold (l.map f)

/-- The evaluations' fold over a family reads the unit exactly where
its seed or a listed member's evaluation does. -/
theorem evalFold_unit {α : Type} (f : α → Poly) (x : BPair) :
    ∀ (l : List α) (s : BPair),
    (l.foldl (fun a u => a * eval (f u) x) s).oneValue BPair.unit
      ↔ (s.oneValue BPair.unit
        ∨ (l.any (fun u => decide ((eval (f u) x).oneValue BPair.unit)))
            = true)
  | [], s => by
    constructor
    · intro h
      exact Or.inl h
    · intro h
      match h with
      | .inl hs => exact hs
      | .inr hb => exact Bool.noConfusion hb
  | u :: l, s => by
    show (l.foldl (fun a u => a * eval (f u) x) (s * eval (f u) x)).oneValue
        BPair.unit
      ↔ (s.oneValue BPair.unit
        ∨ (decide ((eval (f u) x).oneValue BPair.unit)
            || l.any (fun u => decide ((eval (f u) x).oneValue BPair.unit)))
            = true)
    refine (evalFold_unit f x l (s * eval (f u) x)).trans
      ((or_congr (BPair.mul_unit_iff s (eval (f u) x)) Iff.rfl).trans ?_)
    by_cases he : (eval (f u) x).oneValue BPair.unit
    · rw [decide_eq_true he]
      show (s.oneValue BPair.unit ∨ (eval (f u) x).oneValue BPair.unit)
          ∨ _ = true
        ↔ s.oneValue BPair.unit ∨ true = true
      exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl (Or.inr he)⟩
    · rw [decide_eq_false he]
      show (s.oneValue BPair.unit ∨ (eval (f u) x).oneValue BPair.unit)
          ∨ (l.any (fun u => decide ((eval (f u) x).oneValue BPair.unit)))
            = true
        ↔ s.oneValue BPair.unit
          ∨ (l.any (fun u => decide ((eval (f u) x).oneValue BPair.unit)))
            = true
      constructor
      · intro h
        match h with
        | .inl (.inl hs) => exact Or.inl hs
        | .inl (.inr hp) => exact absurd hp he
        | .inr ht => exact Or.inr ht
      · intro h
        match h with
        | .inl hs => exact Or.inl (Or.inl hs)
        | .inr ht => exact Or.inr ht

/-- The family's product fold evaluates to the evaluations' fold over
the family. -/
theorem eval_prodFoldMap {α : Type} (f : α → Poly) (x : BPair)
    (l : List α) :
    (eval (prodFoldMap f l) x).oneValue
      (l.foldl (fun a u => a * eval (f u) x) (eval one x)) := by
  show (eval ((l.map f).foldl mul one) x).oneValue _
  refine BPair.oneValue_trans (eval_prodFold x (l.map f) one) ?_
  rw [ground.foldl_map]
  exact BPair.oneValue_refl _

/-- The factor fold reads the sum's unit at a value exactly where a
listed factor's evaluation does. -/
theorem prodFold_unit (ps : List Poly) (x : BPair) :
    (eval (prodFold ps) x).oneValue BPair.unit
      ↔ (ps.any (fun p => decide ((eval p x).oneValue BPair.unit)))
          = true := by
  refine (BPair.unit_iff (eval_prodFold x ps one)).trans
    ((evalFold_unit (fun p => p) x ps (eval one x)).trans ?_)
  constructor
  · intro h
    match h with
    | Or.inl h1 =>
      exact absurd (BPair.oneValue_trans
        (BPair.oneValue_symm (eval_one (BPair.ofPos Pos.one) x)) h1)
        (BPair.ofPos_off Pos.one)
    | Or.inr h2 => exact h2
  · exact Or.inr

/-- The family's product fold reads the unit at a point exactly where
a listed member's evaluation does. -/
theorem prodFoldMap_unit {α : Type} (f : α → Poly) (x : BPair)
    (l : List α) :
    (eval (prodFoldMap f l) x).oneValue BPair.unit
      ↔ (l.any (fun u => decide ((eval (f u) x).oneValue BPair.unit)))
          = true := by
  refine (prodFold_unit (l.map f) x).trans ?_
  rw [ground.any_map]

/-- A family's product fold off the unit at a point puts every
listed member's evaluation off the unit there. -/
theorem prodFoldMap_off {α : Type} (f : α → Poly) (x : BPair)
    (l : List α) (h : ¬ (eval (prodFoldMap f l) x).oneValue BPair.unit)
    (u : α) (hu : u ∈ l) : ¬ (eval (f u) x).oneValue BPair.unit :=
  fun hx => h ((prodFoldMap_unit f x l).mpr
    (ground.any_of_mem _ hu (decide_eq_true hx)))

/-- The running product reads its accumulator as a left factor:
the fold at a stated accumulator is the accumulator against a
cofactor. -/
private theorem foldAcc : ∀ (t : List Poly) (acc : Poly),
    ∃ B, oneValue (t.foldl mul acc) (mul acc B)
  | [], acc =>
    ⟨one,
      oneValue_symm
        (oneValue_trans (mul_comm acc one)
          (one_mul acc))⟩
  | h :: t, acc =>
    match foldAcc t (mul acc h) with
    | ⟨B, hB⟩ =>
      ⟨mul h B, oneValue_trans hB (mul_assoc acc h B)⟩

/-- Every entry of a factor list divides the running product at a
stated accumulator, the cofactor the fold's own. -/
private theorem foldFactor : ∀ (t : List Poly) (acc : Poly) (j : Nat),
    j < t.length →
    ∃ A, oneValue (mul (ground.getAt [] t j) A)
      (t.foldl mul acc)
  | [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | h :: t, acc, 0, _ =>
    match foldAcc t (mul acc h) with
    | ⟨B, hB⟩ =>
      ⟨mul acc B,
        oneValue_symm
          (oneValue_trans hB
            (oneValue_trans (mul_assoc acc h B)
              (mul_left_comm acc h B)))⟩
  | h :: t, acc, j + 1, hj =>
    foldFactor t (mul acc h) j (Nat.lt_of_succ_lt_succ hj)

/-- Every entry of a factor list divides the factor fold. -/
theorem prodFold_factor : ∀ (l : List Poly) (j : Nat), j < l.length →
    ∃ A, oneValue (mul (ground.getAt [] l j) A) (prodFold l) :=
  fun l j hj => foldFactor l one j hj

/-- The entrywise rescaling is the one-member product, the scale
entering as the constant polynomial at its own key. -/
theorem scaleP_single (c : BPair) (q : Poly) :
    oneValue (scaleP c q) (mul q [c]) :=
  oneValue_trans
    (oneValue_map (fun x => (c * x).norm) (fun d => c * d) q
      (fun x _ => BPair.norm_oneValue (c * x)))
    (oneValue_symm (mul_single q c))

/-- The scale rides either member at the one product, the rescaled
factors exchanged. -/
theorem scaleP_exchange (c : BPair) (p q : Poly) :
    oneValue (mul p (scaleP c q)) (mul q (scaleP c p)) :=
  oneValue_trans (mul_congr p (scaleP_single c q))
    (oneValue_trans (mul_left_comm p q [c])
      (mul_congr q (oneValue_symm (scaleP_single c p))))

/-- The one-member site's product at a ground datum reads the
memberwise rescaling, `BPair.ofPos_scale` carried to the
polynomial carrier. -/
theorem ofPos_scale (w : Pos) (p : Poly) :
    oneValue (mul [BPair.ofPos w] p) (p.map (fun e => e.scale w)) :=
  oneValue_trans (mul_comm [BPair.ofPos w] p)
    (oneValue_trans (mul_single p (BPair.ofPos w))
      (oneValue_map (fun e => BPair.ofPos w * e) (fun e => e.scale w) p (fun x _ => (fun e => BPair.ofPos_scale w e) x)))

/-! The Horner read's own class reads: a unit tail reads the sum's
unit at every argument, and two polynomials reading one value read
one value at every argument. -/

/-- A unit tail reads the sum's unit at every value. -/
theorem eval_unitTail : ∀ {p : Poly}, unitTail p → ∀ r : BPair,
    (eval p r).oneValue BPair.unit
  | [], _, _ => BPair.oneValue_refl _
  | _ :: _, h, r =>
    BPair.oneValue_trans
      (BPair.add_congr h.1
        (BPair.mul_congr (BPair.oneValue_refl r) (eval_unitTail h.2 r)))
      (BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl BPair.unit)
        (BPair.mul_unit r)) (BPair.add_unit BPair.unit))

/-- The Horner read passes the class read: two polynomials reading
one value read one value at every argument. -/
theorem eval_congr : ∀ {p q : Poly}, oneValue p q → ∀ r : BPair,
    (eval p r).oneValue (eval q r)
  | [], [], _, _ => BPair.oneValue_refl _
  | [], d :: q, h, r => BPair.oneValue_symm (eval_unitTail (p := d :: q) h r)
  | c :: p, [], h, r => eval_unitTail (p := c :: p) h r
  | _ :: _, _ :: _, h, r =>
    BPair.add_congr h.1
      (BPair.mul_congr (BPair.oneValue_refl r) (eval_congr h.2 r))

/-- The Horner read collects to the monomial fold. -/
theorem eval_famFold : ∀ (p : Poly) (x : BPair),
    (eval p x).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun k => ground.getAt BPair.unit p k * ground.bpow x k)
        (List.range p.length))
  | [], _ => BPair.oneValue_refl _
  | c :: t, x => by
    rw [show (c :: t).length = t.length + 1 from rfl,
      ground.foldB_range_cons
        (fun k => ground.getAt BPair.unit (c :: t) k * ground.bpow x k)
        t.length]
    refine BPair.add_congr
      (BPair.oneValue_symm (BPair.mul_one_read c)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl x) (eval_famFold t x)) ?_
    refine BPair.oneValue_symm (BPair.oneValue_trans ?_
      (ground.foldB_mul_left x
        (fun j => ground.getAt BPair.unit t j * ground.bpow x j)
        (List.range t.length)))
    refine ground.foldB_congr_members _ _ (List.range t.length)
      (fun j _ => ?_)
    show (ground.getAt BPair.unit t j * ground.bpow x (j + 1)).oneValue
      (x * (ground.getAt BPair.unit t j * ground.bpow x j))
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.norm_oneValue (x * ground.bpow x j))) ?_
    exact BPair.oneValue_of_eq
      (BPair.mul_left_comm (ground.getAt BPair.unit t j) x
        (ground.bpow x j))

/-! `def:ground`'s homogeneity principle at the coefficient list:
the composite point `[ln : c]` reads a polynomial through the
cleared evaluation, and the clearing is itself a coefficient list —
the integer representative of the composite point's read.  Its
reads are the Horner read at the cleared list, the derivative one
power down, and the value's own representative. -/

/-- The variable's clearing at a stated power: each key's coefficient
against the clearing's complementary power, `p̃_k = p_k c^(K−k)`, the
composite point's integer representative. -/
def clearVar (p : Poly) (c : Pos) (K : Nat) : Poly :=
  (List.range p.length).map (fun k =>
    (ground.getAt BPair.unit p k
      * ground.bpow (BPair.ofPos c) (K - k)).norm)

/-- The clearing keeps the key count. -/
theorem length_clearVar (p : Poly) (c : Pos) (K : Nat) :
    (clearVar p c K).length = p.length :=
  (ground.length_map _ (List.range p.length)).trans
    (ground.length_range p.length)

/-- The cleared list's entry below the top: the key's coefficient
against the clearing's complementary power. -/
private theorem clearVar_getAt_lt (p : Poly) (c : Pos) (K k : Nat)
    (h : k < p.length) :
    ground.getAt BPair.unit (clearVar p c K) k
      = (ground.getAt BPair.unit p k
        * ground.bpow (BPair.ofPos c) (K - k)).norm := by
  show ground.getAt BPair.unit ((List.range p.length).map (fun j =>
      (ground.getAt BPair.unit p j
        * ground.bpow (BPair.ofPos c) (K - j)).norm)) k
    = (ground.getAt BPair.unit p k
        * ground.bpow (BPair.ofPos c) (K - k)).norm
  rw [ground.getAt_map_range BPair.unit _ p.length k, if_pos h]

/-- The cleared list's entry at every key: the key's coefficient
against the clearing's complementary power, a key beyond the top
reading the sum's unit at both spellings. -/
theorem getAt_clearVar (p : Poly) (c : Pos) (K k : Nat) :
    (ground.getAt BPair.unit (clearVar p c K) k).oneValue
      ((ground.getAt BPair.unit p k
        * ground.bpow (BPair.ofPos c) (K - k)).norm) := by
  by_cases h : k < p.length
  · exact BPair.oneValue_of_eq (clearVar_getAt_lt p c K k h)
  · show (ground.getAt BPair.unit ((List.range p.length).map (fun j =>
        (ground.getAt BPair.unit p j
          * ground.bpow (BPair.ofPos c) (K - j)).norm)) k).oneValue
      ((ground.getAt BPair.unit p k
        * ground.bpow (BPair.ofPos c) (K - k)).norm)
    rw [ground.getAt_map_range BPair.unit _ p.length k, if_neg h,
      ground.getAt_over BPair.unit p k (Nat.le_of_not_lt h)]
    exact BPair.oneValue_symm
      (BPair.oneValue_trans (BPair.norm_oneValue _)
        (BPair.unit_mul _))

/-- The clearing at every representative of one value, at one stated
power: a further key reads the unit either way. -/
theorem clearVar_congr {p q : Poly} (h : oneValue p q) (c : Pos)
    (K : Nat) : oneValue (clearVar p c K) (clearVar q c K) :=
  ov_of_getAt (fun k =>
    BPair.oneValue_trans (getAt_clearVar p c K k)
      (BPair.oneValue_trans (BPair.norm_oneValue _)
        (BPair.oneValue_trans
          (BPair.mul_congr_left (oneValue_getAt k h))
          (BPair.oneValue_trans
            (BPair.oneValue_symm (BPair.norm_oneValue _))
            (BPair.oneValue_symm (getAt_clearVar q c K k))))))

/-- The clearing at a leading key: the key's own coefficient against
the whole power, the tail's clearing one power down. -/
theorem clearVar_cons (a : BPair) (t : Poly) (c : Pos)
    (K : Nat) :
    clearVar (a :: t) c K
      = (a * ground.bpow (BPair.ofPos c) K).norm
        :: clearVar t c (K - 1) := by
  refine ground.getAt_ext BPair.unit _ _ ?_ ?_
  · rw [length_clearVar (a :: t) c K]
    show t.length + 1 = (clearVar t c (K - 1)).length + 1
    rw [length_clearVar t c (K - 1)]
  · intro i hi
    rw [length_clearVar (a :: t) c K] at hi
    match i with
    | 0 =>
      rw [clearVar_getAt_lt (a :: t) c K 0 hi]
      rfl
    | j + 1 =>
      have hj : j < t.length := Nat.lt_of_succ_lt_succ hi
      rw [clearVar_getAt_lt (a :: t) c K (j + 1) hi]
      show (ground.getAt BPair.unit t j
          * ground.bpow (BPair.ofPos c) (K - (j + 1))).norm
        = ground.getAt BPair.unit (clearVar t c (K - 1)) j
      rw [clearVar_getAt_lt t c (K - 1) j hj, ground.subSub K 1 j,
        Nat.add_comm 1 j]

/-- The cleared evaluation collects to the monomial fold: the
coefficient against the point's power and the clearing's
complementary power, key by key. -/
theorem evalClear_read (p : Poly) (ln : BPair) (c : Pos)
    (K : Nat) :
    (evalClear p ln c K).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun k => ground.getAt BPair.unit p k * ground.bpow ln k
          * ground.bpow (BPair.ofPos c) (K - k))
        (List.range p.length)) := by
  match p with
  | [] => exact BPair.oneValue_refl _
  | a :: t =>
  refine BPair.oneValue_trans
    (evalClearGo_read ln (BPair.ofPos c) (a :: t) BPair.unit
      (BPair.ofPos Pos.one) (K + 1)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.unit_mul _) (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans (BPair.unit_add _) ?_
  refine ground.famFold_congr_members_ov BPair.oneValue BPair.add
    BPair.unit BPair.oneValue_refl BPair.add_congr _ _
    (List.range (a :: t).length) (fun j _ => ?_)
  exact BPair.mul_congr_left
    (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_comm _ _))
        (BPair.mul_one_read _)))

/-- The cleared list's Horner read is the cleared evaluation. -/
theorem eval_clearVar (p : Poly) (c : Pos) (K : Nat) (l : BPair) :
    (eval (clearVar p c K) l).oneValue (evalClear p l c K) := by
  refine BPair.oneValue_trans (eval_famFold (clearVar p c K) l) ?_
  rw [length_clearVar p c K]
  refine BPair.oneValue_trans ?_
    (BPair.oneValue_symm (evalClear_read p l c K))
  refine ground.foldB_congr_members _ _ (List.range p.length) ?_
  intro i _
  refine BPair.oneValue_trans
    (BPair.mul_congr_left (getAt_clearVar p c K i)) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr_left (BPair.norm_oneValue _)) ?_
  exact BPair.oneValue_of_eq
    (BPair.mul_right_comm (ground.getAt BPair.unit p i)
      (ground.bpow (BPair.ofPos c) (K - i)) (ground.bpow l i))

/-- A one-key list's cleared read is its coefficient against the whole
clearing. -/
theorem evalClear_single (c ln : BPair) (cc : Pos) (N : Nat) :
    (evalClear [c] ln cc N).oneValue
      (c * ground.bpow (BPair.ofPos cc) N) := by
  refine BPair.oneValue_trans (evalClear_read [c] ln cc N) ?_
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  exact BPair.mul_congr_left (BPair.mul_one_read c)

/-- The cleared evaluation is one value across the polynomial's
representatives, the clearing's congruence read through the
evaluation's. -/
theorem evalClear_congr {p q : Poly} (h : oneValue p q)
    (ln : BPair) (c : Pos) (K : Nat) :
    (evalClear p ln c K).oneValue (evalClear q ln c K) :=
  ground.BPair.oneValue_trans
    (ground.BPair.oneValue_symm (eval_clearVar p c K ln))
    (ground.BPair.oneValue_trans (eval_congr (clearVar_congr h c K) ln)
      (eval_clearVar q c K ln))

/-- The cleared evaluation at a scaled point: the point's numerator
and denominator scaled by one positive read the scale's power at the
clearing against the original evaluation, the homogeneity
principle's display at the cleared carrier, the keys within the
clearing power. -/
theorem evalClear_scalePoint (p : Poly) (xN : BPair) (c w : Pos)
    (K : Nat) (hp : p.length ≤ K + 1) :
    (evalClear p (xN * BPair.ofPos w) (c * w) K).oneValue
      (ground.bpow (BPair.ofPos w) K * evalClear p xN c K) := by
  refine BPair.oneValue_trans
    (evalClear_read p (xN * BPair.ofPos w) (c * w) K) ?_
  refine BPair.oneValue_trans ?_
    (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (evalClear_read p xN c K)))
  refine BPair.oneValue_trans ?_
    (ground.foldB_mul_left (ground.bpow (BPair.ofPos w) K) _
      (List.range p.length))
  refine ground.foldB_congr_members _ _ (List.range p.length) ?_
  intro k hk
  rw [ground.countOf_range k p.length] at hk
  by_cases hklt : k < p.length
  · have hkK : k ≤ K :=
      Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hklt hp)
    obtain ⟨g, hg⟩ := Nat.le.dest hkK
    have he : k + (K - k) = K := by
      rw [← hg, ground.addSubSelfL]
    have hWK : (ground.bpow (BPair.ofPos w) K).oneValue
        (ground.bpow (BPair.ofPos w) k
          * ground.bpow (BPair.ofPos w) (K - k)) := by
      have h0 := ground.bpow_add (BPair.ofPos w) k (K - k)
      rw [he] at h0
      exact h0
    refine BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.mul_congr (BPair.oneValue_refl _)
          (ground.bpow_mul xN (BPair.ofPos w) k))
        (BPair.oneValue_trans
          (ground.bpow_congr
            (BPair.oneValue_symm (BPair.ofPos_mul c w)) (K - k))
          (ground.bpow_mul (BPair.ofPos c) (BPair.ofPos w) (K - k)))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq ?_)
      (BPair.mul_congr (BPair.oneValue_symm hWK)
        (BPair.oneValue_refl _))
    rw [← BPair.mul_assoc (ground.getAt BPair.unit p k)
        (ground.bpow xN k) (ground.bpow (BPair.ofPos w) k),
      ← BPair.mul_assoc
        (ground.getAt BPair.unit p k * ground.bpow xN k
          * ground.bpow (BPair.ofPos w) k)
        (ground.bpow (BPair.ofPos c) (K - k))
        (ground.bpow (BPair.ofPos w) (K - k)),
      BPair.mul_right_comm
        (ground.getAt BPair.unit p k * ground.bpow xN k)
        (ground.bpow (BPair.ofPos w) k)
        (ground.bpow (BPair.ofPos c) (K - k)),
      BPair.mul_assoc
        (ground.getAt BPair.unit p k * ground.bpow xN k
          * ground.bpow (BPair.ofPos c) (K - k))
        (ground.bpow (BPair.ofPos w) k)
        (ground.bpow (BPair.ofPos w) (K - k)),
      BPair.mul_comm
        (ground.getAt BPair.unit p k * ground.bpow xN k
          * ground.bpow (BPair.ofPos c) (K - k))
        (ground.bpow (BPair.ofPos w) k
          * ground.bpow (BPair.ofPos w) (K - k))]
  · rw [if_neg hklt] at hk
    exact absurd hk (Nat.lt_irrefl 0)

/-- The cleared evaluation moves across the point's one-value
read. -/
theorem evalClear_congrPoint (p : Poly) {x y : BPair}
    (h : x.oneValue y) (c : Pos) (K : Nat) :
    (evalClear p x c K).oneValue (evalClear p y c K) := by
  refine BPair.oneValue_trans (evalClear_read p x c K) ?_
  refine BPair.oneValue_trans ?_
    (BPair.oneValue_symm (evalClear_read p y c K))
  refine ground.foldB_congr_members _ _ (List.range p.length) ?_
  intro k _
  exact BPair.mul_congr
    (BPair.mul_congr (BPair.oneValue_refl _) (ground.bpow_congr h k))
    (BPair.oneValue_refl _)

/-- The cleared evaluation at a raised clearing power: the raise
collects as the clearing's own power, the keys within the stated
power. -/
theorem evalClear_pow (p : Poly) (x : BPair) (c : Pos)
    (K J : Nat) (hp : p.length ≤ J + 1) (hJK : J ≤ K) :
    (evalClear p x c K).oneValue
      (ground.bpow (BPair.ofPos c) (K - J) * evalClear p x c J) := by
  refine BPair.oneValue_trans (evalClear_read p x c K) ?_
  refine BPair.oneValue_trans ?_
    (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (evalClear_read p x c J)))
  refine BPair.oneValue_trans ?_
    (ground.foldB_mul_left (ground.bpow (BPair.ofPos c) (K - J)) _
      (List.range p.length))
  refine ground.foldB_congr_members _ _ (List.range p.length) ?_
  intro k hk
  rw [ground.countOf_range k p.length] at hk
  by_cases hklt : k < p.length
  · have hkJ : k ≤ J :=
      Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hklt hp)
    obtain ⟨g, hg⟩ := Nat.le.dest hkJ
    obtain ⟨w, hw⟩ := Nat.le.dest hJK
    have h1 : J - k = g := by
      rw [← hg, ground.addSubSelfL]
    have h2 : K - J = w := by
      rw [← hw, ground.addSubSelfL]
    have h3 : K = k + (g + w) := by
      rw [← hw, ← hg, Nat.add_assoc]
    have h4 : K - k = g + w := by
      rw [h3, ground.addSubSelfL]
    rw [h1, h2, h4]
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (ground.bpow_add (BPair.ofPos c) g w)) ?_
    refine BPair.oneValue_of_eq ?_
    rw [← BPair.mul_assoc
        (ground.getAt BPair.unit p k * ground.bpow x k)
        (ground.bpow (BPair.ofPos c) g)
        (ground.bpow (BPair.ofPos c) w),
      BPair.mul_comm
        (ground.getAt BPair.unit p k * ground.bpow x k
          * ground.bpow (BPair.ofPos c) g)
        (ground.bpow (BPair.ofPos c) w)]
  · rw [if_neg hklt] at hk
    exact absurd hk (Nat.lt_irrefl 0)

/-- The cleared evaluation at an end-shaped list: with every middle
coefficient at the sum's unit, the constant key survives at the
clearing's full power and the top key at the point's, the middle
fold absorbing. -/
theorem evalClear_ends (a b : BPair) (mid : List BPair)
    (hmid : unitTail mid) (ln : BPair) (c : Pos) :
    (evalClear (a :: (mid ++ [b])) ln c (mid.length + 1)).oneValue
      (ground.bpow (BPair.ofPos c) (mid.length + 1) * a
        + ground.bpow ln (mid.length + 1) * b) := by
  have hlen : (a :: (mid ++ [b])).length = mid.length + 1 + 1 := by
    show (mid ++ [b]).length + 1 = mid.length + 1 + 1
    rw [ground.length_append mid [b]]
    rfl
  refine BPair.oneValue_trans
    (evalClear_read (a :: (mid ++ [b])) ln c (mid.length + 1)) ?_
  rw [hlen]
  refine BPair.oneValue_trans
    (ground.foldB_range_snoc _ (mid.length + 1)) ?_
  have htop : (ground.getAt BPair.unit (a :: (mid ++ [b]))
        (mid.length + 1)
      * ground.bpow ln (mid.length + 1)
      * ground.bpow (BPair.ofPos c)
          (mid.length + 1 - (mid.length + 1))).oneValue
      (ground.bpow ln (mid.length + 1) * b) := by
    rw [show ground.getAt BPair.unit (a :: (mid ++ [b]))
          (mid.length + 1) = b from
        ground.getAt_append_add BPair.unit mid [b] 0,
      Nat.sub_self (mid.length + 1)]
    exact BPair.oneValue_trans (BPair.mul_one_read _)
      (BPair.oneValue_of_eq (BPair.mul_comm b _))
  have hmids : ∀ j, 0 < ground.countOf j (List.range mid.length) →
      ((fun k => ground.getAt BPair.unit (a :: (mid ++ [b])) k
          * ground.bpow ln k
          * ground.bpow (BPair.ofPos c) (mid.length + 1 - k))
        (j + 1)).oneValue BPair.unit := by
    intro j hj
    have hjm : j < mid.length := by
      rw [ground.countOf_range j mid.length] at hj
      match Nat.lt_or_ge j mid.length with
      | Or.inl h => exact h
      | Or.inr h =>
        rw [if_neg (Nat.not_lt_of_le h)] at hj
        exact absurd hj (Nat.lt_irrefl 0)
    have hm : (ground.getAt BPair.unit (a :: (mid ++ [b]))
        (j + 1)).oneValue BPair.unit := by
      show (ground.getAt BPair.unit (mid ++ [b]) j).oneValue BPair.unit
      rw [show ground.getAt BPair.unit (mid ++ [b]) j
          = ground.getAt BPair.unit mid j from
        (ground.getAt_append BPair.unit mid [b] j).trans
          (if_pos hjm)]
      exact getAt_unitTail hmid j
    exact BPair.oneValue_trans
      (BPair.mul_congr_left
        (BPair.oneValue_trans (BPair.mul_congr_left hm)
          (BPair.unit_mul _)))
      (BPair.unit_mul _)
  have hfold : (ground.famFold BPair.add BPair.unit
      (fun k => ground.getAt BPair.unit (a :: (mid ++ [b])) k
        * ground.bpow ln k
        * ground.bpow (BPair.ofPos c) (mid.length + 1 - k))
      (List.range (mid.length + 1))).oneValue
      (ground.bpow (BPair.ofPos c) (mid.length + 1) * a) := by
    rw [ground.range_cons mid.length]
    show ((ground.getAt BPair.unit (a :: (mid ++ [b])) 0
        * ground.bpow ln 0
        * ground.bpow (BPair.ofPos c) (mid.length + 1 - 0))
      + ground.famFold BPair.add BPair.unit _
          ((List.range mid.length).map (fun j => j + 1))).oneValue _
    rw [ground.famFold_map BPair.add BPair.unit _ (fun j => j + 1)
      (List.range mid.length)]
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans (BPair.mul_congr_left (BPair.mul_one_read a))
          (BPair.oneValue_of_eq (BPair.mul_comm a _)))
        (ground.foldB_null _ (List.range mid.length) hmids)) ?_
    exact BPair.add_unit _
  exact BPair.add_congr hfold htop

/-- The shifted derivative of a cleared list is the shifted
derivative's clearing at the one power. -/
private theorem derivFrom_clearVar :
    ∀ (n : Pos) (t : Poly) (c : Pos) (M : Nat),
      oneValue (derivFrom n (clearVar t c M))
        (clearVar (derivFrom n t) c M)
  | _, [], _, _ => trivial
  | n, a :: t, c, M => by
    rw [clearVar_cons a t c M]
    show oneValue
      (((a * ground.bpow (BPair.ofPos c) M).norm).scale n
        :: derivFrom (succ n) (clearVar t c (M - 1)))
      (clearVar (a.scale n :: derivFrom (succ n) t) c M)
    rw [clearVar_cons (a.scale n) (derivFrom (succ n) t) c M]
    exact ⟨BPair.oneValue_trans
        (BPair.scale_congr n (BPair.norm_oneValue _))
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq
            (ground.BPair.scale_mul_left a (ground.bpow (BPair.ofPos c) M) n))
          (BPair.oneValue_symm (BPair.norm_oneValue _))),
      derivFrom_clearVar (succ n) t c (M - 1)⟩

/-- The derivative of the cleared list is the derivative's clearing,
one power down: `(k+1) p_{k+1} c^(K−1−k)` either way. -/
theorem deriv_clearVar (p : Poly) (c : Pos) (K : Nat) :
    oneValue (deriv (clearVar p c K)) (clearVar (deriv p) c (K - 1)) := by
  match p with
  | [] => exact trivial
  | a :: t =>
    rw [clearVar_cons a t c K]
    exact derivFrom_clearVar Pos.one t c (K - 1)

/-- A memberwise-representative family is its own memberwise
representative. -/
private theorem pnorm_normMap {α : Type} (f : α → BPair) :
    ∀ l : List α, pnorm (l.map (fun x => (f x).norm))
      = l.map (fun x => (f x).norm)
  | [] => rfl
  | a :: t => by
    show ((f a).norm).norm :: pnorm (t.map (fun x => (f x).norm))
      = (f a).norm :: t.map (fun x => (f x).norm)
    rw [BPair.norm_congr (BPair.norm_oneValue (f a)), pnorm_normMap f t]

/-- The clearing's entries are their own memberwise
representatives. -/
private theorem pnorm_clearVar (p : Poly) (c : Pos) (K : Nat) :
    pnorm (clearVar p c K) = clearVar p c K :=
  pnorm_normMap (fun k => ground.getAt BPair.unit p k
      * ground.bpow (BPair.ofPos c) (K - k))
    (List.range p.length)

/-- A single occupied key stands under the length gauge's tail
test. -/
private theorem trim_single_off {x : BPair}
    (h : ¬ x.oneValue BPair.unit) : trim [x] = [x] := by
  show (if decide (x.oneValue BPair.unit) then [] else [x]) = [x]
  exact if_neg (fun hh => h (of_decide_eq_true hh))

/-- Two keys at a tail already standing under the length gauge's
test stand together. -/
private theorem trim_cons_cons (x y : BPair) (r : Poly)
    (h : trim (y :: r) = y :: r) : trim (x :: y :: r) = x :: y :: r := by
  show (match trim (y :: r) with
    | [] => if decide (x.oneValue BPair.unit) then [] else [x]
    | d :: t' => x :: d :: t') = x :: y :: r
  rw [h]

/-- The clearing of a trimmed list stands under the length gauge's
tail test: each entry's clearing power sits off the sum's unit, so
the trimmed top stays occupied. -/
private theorem trim_clearVar : ∀ (l : Poly) (c : Pos) (K : Nat),
    trim (clearVar (trim l) c K) = clearVar (trim l) c K
  | [], _, _ => rfl
  | a :: t, c, K => by
    show trim (clearVar (match trim t with
        | [] => if decide (a.oneValue BPair.unit) then [] else [a]
        | d :: t' => a :: d :: t') c K)
      = clearVar (match trim t with
        | [] => if decide (a.oneValue BPair.unit) then [] else [a]
        | d :: t' => a :: d :: t') c K
    cases htr : trim t with
    | nil =>
      cases ha : decide (a.oneValue BPair.unit) with
      | true => rfl
      | false =>
        have hoff : ¬ ((a * ground.bpow (BPair.ofPos c) K).norm).oneValue
            BPair.unit := fun hu =>
          match (BPair.mul_unit_iff a
              (ground.bpow (BPair.ofPos c) K)).mp
              (BPair.oneValue_trans
                (BPair.oneValue_symm (BPair.norm_oneValue _)) hu) with
          | .inl h1 => of_decide_eq_false ha h1
          | .inr h2 =>
            ground.bpow_off (BPair.ofPos c) (BPair.ofPos_off c) K h2
        show trim (clearVar [a] c K) = clearVar [a] c K
        rw [clearVar_cons a [] c K]
        exact trim_single_off hoff
    | cons d t' =>
      have hIH : trim (clearVar (d :: t') c (K - 1))
          = clearVar (d :: t') c (K - 1) := by
        rw [← htr]
        exact trim_clearVar t c (K - 1)
      rw [clearVar_cons a (d :: t') c K,
        clearVar_cons d t' c (K - 1)]
      rw [clearVar_cons d t' c (K - 1)] at hIH
      exact trim_cons_cons _ _ _ hIH

/-- The representative's clearing is its own representative: the
entries enter normed and the top's positive rescaling keeps it off
the unit. -/
theorem vnorm_clearVar (p : Poly) (c : Pos) (K : Nat) :
    vnorm (clearVar (vnorm p) c K) = clearVar (vnorm p) c K := by
  show trim (pnorm (clearVar (vnorm p) c K))
    = clearVar (vnorm p) c K
  rw [pnorm_clearVar (vnorm p) c K]
  exact trim_clearVar (pnorm p) c K

/-! The clearing's ring reads: `def:poly`'s displayed sum, swap and
convolution pass the clearing, the sum and the swap at the one
stated power and the convolution at the joined power with each
factor within its own. -/

/-- The clearing at a sum: componentwise at the one stated power. -/
theorem clearVar_add (p q : Poly) (c : Pos) (K : Nat) :
    oneValue (clearVar (add p q) c K) (add (clearVar p c K) (clearVar q c K)) :=
  ov_of_getAt (fun k =>
    BPair.oneValue_trans (getAt_clearVar (add p q) c K k)
      (BPair.oneValue_trans (BPair.norm_oneValue _)
        (BPair.oneValue_trans
          (BPair.mul_congr_left (getAt_add p q k))
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (BPair.right_distrib _ _ _))
            (BPair.oneValue_trans
              (BPair.add_congr
                (BPair.oneValue_symm (BPair.norm_oneValue _))
                (BPair.oneValue_symm (BPair.norm_oneValue _)))
              (BPair.oneValue_trans
                (BPair.add_congr
                  (BPair.oneValue_symm (getAt_clearVar p c K k))
                  (BPair.oneValue_symm (getAt_clearVar q c K k)))
                (BPair.oneValue_symm
                  (getAt_add (clearVar p c K) (clearVar q c K) k))))))))

/-- The clearing at the memberwise swap. -/
theorem clearVar_neg (p : Poly) (c : Pos) (K : Nat) :
    clearVar (neg p) c K = neg (clearVar p c K) := by
  have hlen : (neg p).length = p.length := ground.length_map BPair.swap p
  have hlen2 : (neg (clearVar p c K)).length = (clearVar p c K).length :=
    ground.length_map BPair.swap (clearVar p c K)
  refine ground.getAt_ext BPair.unit _ _ ?_ ?_
  · rw [length_clearVar (neg p) c K, hlen, hlen2,
      length_clearVar p c K]
  · intro i hi
    rw [length_clearVar (neg p) c K] at hi
    have hi' : i < p.length := by
      rw [← hlen]
      exact hi
    rw [clearVar_getAt_lt (neg p) c K i hi, getAt_neg p i,
      BPair.swap_mul, BPair.norm_swap,
      getAt_neg (clearVar p c K) i, clearVar_getAt_lt p c K i hi']

/-- A key within the second factor's stated power splits the joined
power: the scale's own power against the key's complementary
power. -/
private theorem clearVar_powSplit (a x : BPair) (c : Pos)
    (K1 K2 k : Nat) (hk : k ≤ K2) :
    ((a * x) * ground.bpow (BPair.ofPos c) (K1 + K2 - k)).oneValue
      ((a * ground.bpow (BPair.ofPos c) K1)
        * (x * ground.bpow (BPair.ofPos c) (K2 - k))) := by
  rw [← ground.addSubAssoc hk K1]
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl (a * x))
      (ground.bpow_add (BPair.ofPos c) K1 (K2 - k))) ?_
  exact BPair.oneValue_of_eq
    (BPair.mul_mul_mul_comm a x (ground.bpow (BPair.ofPos c) K1)
      (ground.bpow (BPair.ofPos c) (K2 - k)))

/-- The clearing of a rescaled list at the joined power is the
clearing's own rescaling by the scale at its stated power, a key
beyond the list's top reading the sum's unit either way. -/
private theorem clearVar_scaleMap (a : BPair) (c : Pos) (K1 K2 : Nat)
    (q : Poly) (hq : q.length ≤ K2 + 1) :
    oneValue (clearVar (q.map (fun d => a * d)) c (K1 + K2))
      ((clearVar q c K2).map
        (fun d => (a * ground.bpow (BPair.ofPos c) K1).norm * d)) := by
  refine ov_of_getAt (fun k => ?_)
  have hmid : ((a * ground.getAt BPair.unit q k)
      * ground.bpow (BPair.ofPos c) (K1 + K2 - k)).oneValue
      ((a * ground.bpow (BPair.ofPos c) K1)
        * (ground.getAt BPair.unit q k
          * ground.bpow (BPair.ofPos c) (K2 - k))) := by
    by_cases hk : k ≤ K2
    · exact clearVar_powSplit a (ground.getAt BPair.unit q k) c K1 K2 k hk
    · rw [ground.getAt_over BPair.unit q k
        (Nat.le_trans hq (Nat.lt_of_not_le hk))]
      refine BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.mul_unit a)) ?_
      refine BPair.oneValue_trans (BPair.unit_mul _) ?_
      refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) (BPair.unit_mul _)) ?_
      exact BPair.mul_unit _
  refine BPair.oneValue_trans
    (getAt_clearVar (q.map (fun d => a * d)) c (K1 + K2) k) ?_
  refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr_left (getAt_scale a q k)) ?_
  refine BPair.oneValue_trans hmid ?_
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans
    (getAt_scale (a * ground.bpow (BPair.ofPos c) K1).norm
      (clearVar q c K2) k) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.norm_oneValue _)
      (getAt_clearVar q c K2 k)) ?_
  exact BPair.mul_congr (BPair.oneValue_refl _) (BPair.norm_oneValue _)

/-- The convolution's clearing at the joined power against the
clearings' own convolution, the recursion on the first factor's
stated power: the leading key's scale at its own power and the
shifted product one power down. -/
private theorem clearVar_mul_go :
    ∀ (K1 : Nat) (p q : Poly) (c : Pos) (K2 : Nat),
      p.length ≤ K1 + 1 → q.length ≤ K2 + 1 →
      oneValue (clearVar (mul p q) c (K1 + K2))
        (mul (clearVar p c K1) (clearVar q c K2))
  | _, [], _, _, _, _, _ => trivial
  | 0, [a], q, c, K2, _, hq => by
    show oneValue
      (clearVar (add (q.map (fun d => a * d)) [BPair.unit]) c (0 + K2))
      (mul (clearVar [a] c 0) (clearVar q c K2))
    refine oneValue_trans
      (clearVar_add (q.map (fun d => a * d)) [BPair.unit] c (0 + K2)) ?_
    show oneValue
      (add (clearVar (q.map (fun d => a * d)) c (0 + K2))
        (clearVar [BPair.unit] c (0 + K2)))
      (add ((clearVar q c K2).map
          (fun d => (a * ground.bpow (BPair.ofPos c) 0).norm * d))
        [BPair.unit])
    refine add_congr (clearVar_scaleMap a c 0 K2 q hq) ?_
    show oneValue
      [(BPair.unit * ground.bpow (BPair.ofPos c) (0 + K2)).norm]
      [BPair.unit]
    exact cons_ov
      (BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.unit_mul _))
      trivial
  | 0, _ :: _ :: _, _, _, _, hp, _ =>
    absurd (Nat.le_of_succ_le_succ hp) (Nat.not_succ_le_zero _)
  | k + 1, a :: p', q, c, K2, hp, hq => by
    have hidx : k + 1 + K2 - 1 = k + K2 := by
      rw [Nat.add_right_comm k 1 K2]
      exact ground.addSubSelfR (k + K2) 1
    have hIH := clearVar_mul_go k p' q c K2
      (Nat.le_of_succ_le_succ hp) hq
    show oneValue
      (clearVar (add (q.map (fun d => a * d))
        (BPair.unit :: mul p' q)) c (k + 1 + K2))
      (mul (clearVar (a :: p') c (k + 1)) (clearVar q c K2))
    refine oneValue_trans
      (clearVar_add (q.map (fun d => a * d))
        (BPair.unit :: mul p' q) c (k + 1 + K2)) ?_
    rw [clearVar_cons a p' c (k + 1),
      clearVar_cons BPair.unit (mul p' q) c (k + 1 + K2), hidx]
    show oneValue
      (add (clearVar (q.map (fun d => a * d)) c (k + 1 + K2))
        ((BPair.unit * ground.bpow (BPair.ofPos c) (k + 1 + K2)).norm
          :: clearVar (mul p' q) c (k + K2)))
      (add ((clearVar q c K2).map
          (fun d => (a * ground.bpow (BPair.ofPos c) (k + 1)).norm * d))
        (BPair.unit :: mul (clearVar p' c k) (clearVar q c K2)))
    exact add_congr (clearVar_scaleMap a c (k + 1) K2 q hq)
      (cons_ov
        (BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.unit_mul _))
        hIH)

/-- The clearing at a product: the convolution's clearing at the
joined power is the clearings' own convolution, each factor within
its stated power. -/
theorem clearVar_mul (p q : Poly) (c : Pos) (K1 K2 : Nat)
    (hp : p.length ≤ K1 + 1) (hq : q.length ≤ K2 + 1) :
    oneValue (clearVar (mul p q) c (K1 + K2))
      (mul (clearVar p c K1) (clearVar q c K2)) :=
  clearVar_mul_go K1 p q c K2 hp hq

/-- The cleared evaluation at a sum: the summands' own, at the one
stated power. -/
theorem evalClear_add (p q : Poly) (ln : BPair) (c : Pos) (K : Nat) :
    (evalClear (add p q) ln c K).oneValue
      (evalClear p ln c K + evalClear q ln c K) :=
  BPair.oneValue_trans
    (BPair.oneValue_symm (eval_clearVar (add p q) c K ln))
    (BPair.oneValue_trans (eval_congr (clearVar_add p q c K) ln)
      (BPair.oneValue_trans
        (eval_add (clearVar p c K) (clearVar q c K) ln)
        (BPair.add_congr (eval_clearVar p c K ln)
          (eval_clearVar q c K ln))))

/-- The cleared evaluation at the memberwise swap: the evaluation's
balance partner. -/
theorem evalClear_neg (p : Poly) (ln : BPair) (c : Pos) (K : Nat) :
    (evalClear (neg p) ln c K).oneValue
      (evalClear p ln c K).swap :=
  BPair.oneValue_trans
    (BPair.oneValue_symm (eval_clearVar (neg p) c K ln))
    (BPair.oneValue_trans
      (BPair.oneValue_of_eq (by
        rw [clearVar_neg p c K, eval_neg (clearVar p c K) ln]))
      (ground.swap_congr (eval_clearVar p c K ln)))

/-- The cleared evaluation at a product: the factors' own evaluations at
the split powers, each factor within its stated power. -/
theorem evalClear_mul (p q : Poly) (ln : BPair) (c : Pos)
    (K1 K2 : Nat) (hp : p.length ≤ K1 + 1) (hq : q.length ≤ K2 + 1) :
    (evalClear (mul p q) ln c (K1 + K2)).oneValue
      (evalClear p ln c K1 * evalClear q ln c K2) :=
  BPair.oneValue_trans
    (BPair.oneValue_symm (eval_clearVar (mul p q) c (K1 + K2) ln))
    (BPair.oneValue_trans
      (eval_congr (clearVar_mul p q c K1 K2 hp hq) ln)
      (BPair.oneValue_trans
        (eval_mul (clearVar p c K1) (clearVar q c K2) ln)
        (BPair.mul_congr (eval_clearVar p c K1 ln)
          (eval_clearVar q c K2 ln))))

/-- The rescaled list's clearing is the clearing's own rescaling,
entry by entry at the stated power. -/
private theorem clearVar_scaleP (a : BPair) (p : Poly) (c : Pos)
    (K : Nat) :
    oneValue (clearVar (scaleP a p) c K)
      ((clearVar p c K).map (fun d => a * d)) :=
  ov_of_getAt (fun k =>
    BPair.oneValue_trans (getAt_clearVar (scaleP a p) c K k)
      (BPair.oneValue_trans (BPair.norm_oneValue _)
        (BPair.oneValue_trans
          (BPair.mul_congr_left (getAt_scaleP a p k))
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq
              (BPair.mul_assoc a (ground.getAt BPair.unit p k)
                (ground.bpow (BPair.ofPos c) (K - k))))
            (BPair.oneValue_trans
              (BPair.mul_congr (BPair.oneValue_refl a)
                (BPair.oneValue_symm
                  (BPair.oneValue_trans (getAt_clearVar p c K k)
                    (BPair.norm_oneValue _))))
              (BPair.oneValue_symm
                (getAt_scale a (clearVar p c K) k)))))))

/-- The cleared evaluation at a rescaled list: the scale's multiple
of the list's own, at the one stated power. -/
theorem evalClear_scaleP (a : BPair) (p : Poly) (ln : BPair) (c : Pos)
    (K : Nat) :
    (evalClear (scaleP a p) ln c K).oneValue (a * evalClear p ln c K) :=
  BPair.oneValue_trans
    (BPair.oneValue_symm (eval_clearVar (scaleP a p) c K ln))
    (BPair.oneValue_trans
      (eval_congr (clearVar_scaleP a p c K) ln)
      (BPair.oneValue_trans (eval_scale (clearVar p c K) a ln)
        (BPair.mul_congr (BPair.oneValue_refl a)
          (eval_clearVar p c K ln))))

/-- A one-key remainder list reads its own single member: at a
stated value of the Horner read the list is that value's own
one-key list. -/
private theorem lenOne_read : ∀ R : Poly, R.length = 1 →
    ∀ x v : BPair, (eval R x).oneValue v → oneValue R [v]
  | [], h, _, _, _ => Nat.noConfusion h
  | [r], _, x, _, hv =>
    ⟨BPair.oneValue_trans (BPair.oneValue_symm (eval_one r x)) hv,
      trivial⟩
  | _ :: _ :: _, h, _, _, _ => Nat.noConfusion (Nat.succ.inj h)

/-- The monic linear factor `⟨z : c⟩` reads the sum's unit at its own
root: the Horner read of `c + z` at `c`'s balance partner is the two
members' join. -/
theorem eval_monic_linear (c : BPair) :
    (eval (monic [c]) c.swap).oneValue BPair.unit := by
  show (c + c.swap * (BPair.ofPos Pos.one + c.swap * BPair.unit)).oneValue
    BPair.unit
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl c)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl c.swap)
          (BPair.oneValue_trans
            (BPair.add_congr (BPair.oneValue_refl (BPair.ofPos Pos.one))
              (BPair.mul_unit c.swap))
            (BPair.add_unit (BPair.ofPos Pos.one))))
        (ground.BPair.mul_one_read c.swap))) ?_
  exact ground.unitOfOne (BPair.oneValue_refl c)

/-- The division at a linear divisor leaves the Horner read at the
divisor's own root: dividing by the monic `⟨x : c⟩` the remainder is
the one-key list of the polynomial's value at `c`'s balance partner,
`def:poly`'s division display at a linear factor. -/
theorem div_linear_eval (c : BPair) (P : Poly) :
    oneValue (div [c] P).2 [eval P c.swap] := by
  refine lenOne_read (div [c] P).2 (div_len [c] P) c.swap
    (eval P c.swap) ?_
  have hmc : (eval (monic [c]) c.swap).oneValue BPair.unit :=
    eval_monic_linear c
  have hA : (eval (mul (monic [c]) (div [c] P).1) c.swap).oneValue
      BPair.unit :=
    BPair.oneValue_trans (eval_mul (monic [c]) (div [c] P).1 c.swap)
      (BPair.oneValue_trans
        (BPair.mul_congr hmc (BPair.oneValue_refl (eval (div [c] P).1 c.swap)))
        (BPair.unit_mul (eval (div [c] P).1 c.swap)))
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.unit_add (eval (div [c] P).2 c.swap))) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_symm hA)
      (BPair.oneValue_refl (eval (div [c] P).2 c.swap))) ?_
  exact BPair.oneValue_trans
    (BPair.oneValue_symm
      (eval_add (mul (monic [c]) (div [c] P).1) (div [c] P).2 c.swap))
    (eval_congr (div_identity [c] P) c.swap)

/-- A unit-tail factor carries the product to the unit tail. -/
theorem mul_unitTail (p : Poly) {q : Poly} (h : unitTail q) :
    unitTail (mul p q) :=
  oneValue_unitTail
    (mul_congr p (unitTail_oneValue h (show unitTail [] from trivial)))
    (mul_nil p)

/-! `def:poly`'s top tier and the root reads: the top coefficient at
the largest key, the product's top at the summed key with the
product's own carrier length, the integral read — a product at the
sum's unit puts one factor there — and the roots of a product, of a
power and of a sum. -/

/-- The top coefficient is the entry at the largest key of the
list's own carrier. -/
private theorem top_getAt (p : Poly) (n : Nat) (h : p.length = n + 1) :
    top p = ground.getAt BPair.unit p n := topO_getAt bpairOps p n h

/-- A unit tail's top reads the sum's unit. -/
theorem top_unitTail : ∀ {p : Poly}, unitTail p →
    (top p).oneValue BPair.unit
  | [], _ => BPair.oneValue_refl _
  | [_], h => h.1
  | _ :: c :: t, h => top_unitTail (p := c :: t) h.2

/-- The convolution's carrier at occupied factors: the keys add, the
descent one key per step of the left factor. -/
private theorem mul_len_eq : ∀ (p q : Poly) (n m : Nat),
    p.length = n + 1 → q.length = m + 1 →
    (mul p q).length = n + m + 1
  | [], _, _, _, h, _ => Nat.noConfusion h
  | [_], _, _ + 1, _, h, _ => Nat.noConfusion (Nat.succ.inj h)
  | _ :: _ :: _, _, 0, _, h, _ => Nat.noConfusion (Nat.succ.inj h)
  | [c], q, 0, m, _, hq => by
    have hle : (BPair.unit :: mul ([] : Poly) q).length
        ≤ (q.map (fun d => c * d)).length := by
      rw [ground.length_map, hq]
      exact Nat.succ_le_succ (Nat.zero_le m)
    show (add (q.map (fun d => c * d))
      (BPair.unit :: mul ([] : Poly) q)).length = 0 + m + 1
    rw [add_lenL _ _ hle, ground.length_map, hq, Nat.zero_add]
  | c :: d :: t, q, n + 1, m, h, hq => by
    have hIH : (mul (d :: t) q).length = n + m + 1 :=
      mul_len_eq (d :: t) q n m (Nat.succ.inj h) hq
    have hle : (q.map (fun x => c * x)).length
        ≤ (BPair.unit :: mul (d :: t) q).length := by
      show (q.map (fun x => c * x)).length ≤ (mul (d :: t) q).length + 1
      rw [ground.length_map, hq, hIH]
      exact Nat.succ_le_succ
        (Nat.le_trans (Nat.le_add_left m n) (Nat.le_succ (n + m)))
    show (add (q.map (fun x => c * x))
      (BPair.unit :: mul (d :: t) q)).length = n + 1 + m + 1
    rw [add_lenR _ _ hle]
    show (mul (d :: t) q).length + 1 = n + 1 + m + 1
    rw [hIH, Nat.add_right_comm n 1 m]

/-- The convolution's entry at the summed top key is the two top
entries' product: the key's fold reads one summand at the two tops,
every further summand a factor beyond its own top. -/
private theorem getAt_mul_top : ∀ (m : Nat) (p q : Poly) (n : Nat),
    p.length = n + 1 → q.length = m + 1 →
    (ground.getAt BPair.unit (mul p q) (n + m)).oneValue
      (ground.getAt BPair.unit p n * ground.getAt BPair.unit q m)
  | 0, _, [], _, _, hq => Nat.noConfusion hq
  | 0, _, _ :: _ :: _, _, _, hq => Nat.noConfusion (Nat.succ.inj hq)
  | 0, p, [b], n, _, _ =>
    BPair.oneValue_trans (oneValue_getAt n (mul_single p b))
      (BPair.oneValue_trans (getAt_scale b p n)
        (BPair.oneValue_of_eq
          (BPair.mul_comm b (ground.getAt BPair.unit p n))))
  | m + 1, p, q, n, hp, hq => by
    obtain hnil | ⟨q', b, hqe, hql⟩ := snoc_cases q
    · rw [hnil] at hq
      exact Nat.noConfusion hq
    · have hq'l : q'.length = m + 1 := Nat.succ.inj (hql.trans hq)
      subst hqe
      have hidx : n + (m + 1) = q'.length + n := by
        rw [hq'l]; exact Nat.add_comm n (m + 1)
      have hb : ground.getAt BPair.unit (q' ++ [b]) (m + 1) = b := by
        rw [← hq'l]
        exact ground.getAt_append_add BPair.unit q' [b] 0
      have hlen : (mul p q').length ≤ q'.length + n := by
        refine mul_len p q' ?_ (q'.length + n) ?_
        · rw [hq'l]
          exact Nat.succ_le_succ (Nat.zero_le m)
        · rw [hp]
          show n + 1 + q'.length ≤ q'.length + n + 1
          rw [Nat.add_right_comm n 1 q'.length, Nat.add_comm n q'.length]
          exact Nat.le_refl _
      rw [hidx, hb]
      refine BPair.oneValue_trans
        (oneValue_getAt (q'.length + n) (mul_snoc p q' b)) ?_
      refine BPair.oneValue_trans
        (getAt_add (mul p q')
          (shiftUp q'.length (p.map (fun d => b * d))) (q'.length + n)) ?_
      rw [ground.getAt_over BPair.unit (mul p q') (q'.length + n) hlen,
        getAt_shiftUp_add q'.length (p.map (fun d => b * d)) n]
      exact BPair.oneValue_trans (BPair.unit_add _)
        (BPair.oneValue_trans (getAt_scale b p n)
          (BPair.oneValue_of_eq
            (BPair.mul_comm b (ground.getAt BPair.unit p n))))

/-- At factors of occupied tops the product's top sits at the summed
key, the product's carrier one key below the tops' join. -/
theorem length_mul : ∀ (p q : Poly), 0 < p.length → 0 < q.length →
    (mul p q).length + 1 = p.length + q.length
  | [], _, hp, _ => absurd hp (Nat.lt_irrefl 0)
  | _, [], _, hq => absurd hq (Nat.lt_irrefl 0)
  | _ :: p, _ :: q, _, _ => by
    rw [mul_len_eq _ _ p.length q.length rfl rfl]
    show p.length + q.length + 1 + 1 = p.length + 1 + q.length + 1
    rw [Nat.add_right_comm p.length 1 q.length]

/-- The product's top coefficient is the tops' product, `def:poly`'s
displayed read at the summed key, the vacant factors at the unit's
own product. -/
theorem top_mul : ∀ p q : Poly, (top (mul p q)).oneValue (top p * top q)
  | [], q => BPair.oneValue_symm (BPair.unit_mul (top q))
  | _ :: p, [] =>
    BPair.oneValue_trans (top_unitTail (mul_nil _))
      (BPair.oneValue_symm (BPair.mul_unit _))
  | _ :: p, _ :: q => by
    rw [top_getAt (mul _ _) (p.length + q.length)
        (mul_len_eq _ _ p.length q.length rfl rfl),
      top_getAt _ p.length rfl, top_getAt _ q.length rfl]
    exact getAt_mul_top q.length _ _ p.length rfl rfl

/-- The trimmed list is vacant or carries an occupied top. -/
private theorem trim_top : ∀ l : Poly,
    trim l = [] ∨ ¬ (top (trim l)).oneValue BPair.unit
  | [] => Or.inl rfl
  | c :: t => by
    have ht := trim_top t
    show (match trim t with
      | [] => if decide (c.oneValue BPair.unit) then [] else [c]
      | d :: t' => c :: d :: t') = [] ∨
      ¬ (top (match trim t with
        | [] => if decide (c.oneValue BPair.unit) then [] else [c]
        | d :: t' => c :: d :: t')).oneValue BPair.unit
    cases htr : trim t with
    | nil =>
      cases hc : decide (c.oneValue BPair.unit) with
      | true => exact Or.inl rfl
      | false => exact Or.inr (of_decide_eq_false hc)
    | cons d t' =>
      rw [htr] at ht
      cases ht with
      | inl hnil => exact Nat.noConfusion (congrArg List.length hnil)
      | inr hoff => exact Or.inr hoff

/-- An occupied polynomial's representative carries an occupied
top. -/
theorem vnorm_top {P : Poly} (h : ¬ unitTail P) :
    ¬ (top (vnorm P)).oneValue BPair.unit := by
  cases trim_top (pnorm P) with
  | inl hnil =>
    exact absurd
      (show unitTail P from
        (show oneValue [] P from (show vnorm P = [] from hnil) ▸ vnorm_ov P))
      h
  | inr hoff => exact hoff

/-- The representative's top key carries a coefficient off the sum's
unit. -/
theorem vnorm_len_off {Q : Poly} {m : Nat}
    (hlen : (vnorm Q).length = m + 1) :
    ¬ (ground.getAt BPair.unit Q m).oneValue BPair.unit := by
  intro hu
  have hnot : ¬ unitTail Q := by
    intro hut
    rw [vnorm_congr
      (unitTail_oneValue (q := ([] : Poly)) hut trivial)] at hlen
    exact Nat.noConfusion (show (0 : Nat) = m + 1 from hlen)
  refine vnorm_top hnot ?_
  show (topO ground.bpairOps (vnorm Q)).oneValue BPair.unit
  rw [topO_getAt ground.bpairOps (vnorm Q) m hlen]
  exact BPair.oneValue_trans
    (oneValue_getAt m (vnorm_ov Q)) hu

/-- A list vacant beyond a stated count has its representative
inside it. -/
theorem vnormLen_cap {q : Poly} {N : Nat}
    (h : ∀ j, N ≤ j → (ground.getAt BPair.unit q j).oneValue BPair.unit) :
    (vnorm q).length ≤ N := by
  match hL : (vnorm q).length with
  | 0 => exact Nat.zero_le _
  | i + 1 =>
    match Nat.lt_or_ge i N with
    | Or.inl hlt => exact hlt
    | Or.inr hge => exact absurd (h i hge) (vnorm_len_off hL)

/-- The value's representative sits inside its list's key count, the
cap's read at the vacant overflow. -/
theorem vnormLen_le (q : Poly) :
    (vnorm q).length ≤ q.length :=
  vnormLen_cap (fun j hj =>
    BPair.oneValue_of_eq (ground.getAt_over BPair.unit q j hj))

/-- The integral read: a product at the sum's unit puts one factor's
every coefficient there, the tops' product off the unit at two
occupied representatives. -/
theorem unitTail_mul_of {p q : Poly} (h : unitTail (mul p q)) :
    unitTail p ∨ unitTail q := by
  by_cases hp : unitTail p
  · exact Or.inl hp
  by_cases hq : unitTail q
  · exact Or.inr hq
  have hP := vnorm_top hp
  have hQ := vnorm_top hq
  have hmul : unitTail (mul (vnorm p) (vnorm q)) :=
    oneValue_unitTail (oneValue_symm (mul_vnorm_ov p q)) h
  have hz : ((top (vnorm p)) * (top (vnorm q))).oneValue BPair.unit :=
    BPair.oneValue_trans
      (BPair.oneValue_symm (top_mul (vnorm p) (vnorm q)))
      (top_unitTail hmul)
  exact ((BPair.mul_unit_iff _ _).mp hz).elim (fun x => absurd x hP)
    (fun x => absurd x hQ)

/-- `def:poly`'s shared-factor withdrawal: a shared factor of
occupied top withdraws at two products of one value, the
difference's own factorization against the integral read. -/
theorem pmul_cancel (d u v : Poly) (hd : ¬ unitTail d)
    (h : oneValue (mul d u) (mul d v)) : oneValue u v := by
  have hdiff : unitTail (add (mul d u) (neg (mul d v))) :=
    diff_unitTail h
  have hstep : oneValue (mul d (add u (neg v)))
      (add (mul d u) (neg (mul d v))) := by
    rw [neg_prod d v]
    exact mul_sum d u (neg v)
  have hprod : unitTail (mul d (add u (neg v))) :=
    oneValue_unitTail hstep hdiff
  exact ov_of_diff ((unitTail_mul_of hprod).elim
    (fun hx => absurd hx hd) (fun hx => hx))

/-- A unit-tail factor carries the product to the unit tail, either
side. -/
theorem of_unitTail_mul {p q : Poly} (h : unitTail p ∨ unitTail q) :
    unitTail (mul p q) :=
  h.elim (fun hp => oneValue_unitTail (mul_comm p q) (mul_unitTail q hp))
    (fun hq => mul_unitTail p hq)

/-- An occupied polynomial's powers stay occupied. -/
theorem powOf_occupied {p : Poly} (hp : ¬ unitTail p) :
    ∀ n : Nat, ¬ unitTail (powOf p n)
  | 0, h => ground.BPair.ofPos_off Pos.one h.1
  | n + 1, h => (unitTail_mul_of h).elim hp (powOf_occupied hp n)

/-- The power adds its counts, the product's fold split at a stated
key. -/
theorem powOf_add (p : Poly) : ∀ a b : Nat,
    oneValue (powOf p (a + b)) (mul (powOf p a) (powOf p b))
  | 0, b => by
    rw [Nat.zero_add b]
    exact oneValue_symm (one_mul (powOf p b))
  | a + 1, b => by
    rw [Nat.add_right_comm a 1 b]
    show oneValue (mul p (powOf p (a + b)))
      (mul (mul p (powOf p a)) (powOf p b))
    exact oneValue_trans (mul_congr p (powOf_add p a b))
      (oneValue_symm (mul_assoc p (powOf p a) (powOf p b)))

/-- The root read passes the class read. -/
theorem isRoot_congr {p q : Poly} (h : oneValue p q) {r : BPair}
    (hr : isRoot p r) : isRoot q r :=
  BPair.oneValue_trans (BPair.oneValue_symm (eval_congr h r)) hr

/-- A shared root of two summands is a root of their sum. -/
theorem isRoot_add {p q : Poly} {r : BPair} (hp : isRoot p r)
    (hq : isRoot q r) : isRoot (add p q) r :=
  BPair.oneValue_trans (eval_add p q r)
    (BPair.oneValue_trans (BPair.add_congr hp hq)
      (BPair.add_unit BPair.unit))

/-- The scalar one has no root. -/
theorem isRoot_one (r : BPair) : ¬ isRoot one r := fun h =>
  ground.BPair.ofPos_off Pos.one
    (BPair.oneValue_trans
      (BPair.oneValue_symm (eval_one (BPair.ofPos Pos.one) r)) h)

/-- A product's roots are its factors' own, the Horner values'
integral read. -/
theorem isRoot_mul (p q : Poly) (r : BPair) :
    isRoot (mul p q) r ↔ (isRoot p r ∨ isRoot q r) :=
  ⟨fun h => (BPair.mul_unit_iff (eval p r) (eval q r)).mp
      (BPair.oneValue_trans (BPair.oneValue_symm (eval_mul p q r)) h),
   fun h => BPair.oneValue_trans (eval_mul p q r)
      ((BPair.mul_unit_iff (eval p r) (eval q r)).mpr h)⟩

private theorem isRoot_powOf_succ (p : Poly) (r : BPair) : ∀ n : Nat,
    isRoot (powOf p (n + 1)) r ↔ isRoot p r
  | 0 =>
    ⟨fun h => ((isRoot_mul p (powOf p 0) r).mp h).elim id
        (fun hx => absurd hx (isRoot_one r)),
     fun h => (isRoot_mul p (powOf p 0) r).mpr (Or.inl h)⟩
  | n + 1 =>
    ⟨fun h => ((isRoot_mul p (powOf p (n + 1)) r).mp h).elim id
        (fun hx => (isRoot_powOf_succ p r n).mp hx),
     fun h => (isRoot_mul p (powOf p (n + 1)) r).mpr (Or.inl h)⟩

/-- A positive power's roots are the base's own. -/
theorem isRoot_powOf (p : Poly) (r : BPair) (n : Nat) (hn : 0 < n) :
    isRoot (powOf p n) r ↔ isRoot p r :=
  match n, hn with
  | 0, h => absurd h (Nat.not_succ_le_zero 0)
  | k + 1, _ => isRoot_powOf_succ p r k

private theorem divGo_qlen : ∀ (f : Nat) (stf ptf : List BPair),
    (divGo f stf ptf).1.length + stf.length ≤ ptf.length
      ∨ (divGo f stf ptf).1 = []
  | 0, _, _ => Or.inr rfl
  | f + 1, stf, ptf => by
    by_cases hstop : ptf.length ≤ stf.length
    · rw [divGo_stop (f + 1) stf ptf hstop]
      exact Or.inr rfl
    · match ptf, hstop with
      | [], hstop => exact absurd (Nat.zero_le stf.length) hstop
      | c :: rest, hstop =>
        have hsl : stf.length ≤ rest.length :=
          match Nat.lt_or_ge rest.length stf.length with
          | Or.inl hlt => absurd hlt hstop
          | Or.inr hge => hge
        have hA : (subTop rest (stf.map (fun d => c * d))).length
            = rest.length := subTop_len rest (stf.map (fun d => c * d))
        rw [divGo_cons f stf c rest hstop]
        refine Or.inl ?_
        cases divGo_qlen f stf (subTop rest (stf.map (fun d => c * d))) with
        | inl hle =>
          rw [hA] at hle
          show (divGo f stf (subTop rest (stf.map (fun d => c * d)))).1.length
              + 1 + stf.length ≤ rest.length + 1
          rw [Nat.add_right_comm
            (divGo f stf (subTop rest (stf.map (fun d => c * d)))).1.length
            1 stf.length]
          exact Nat.succ_le_succ hle
        | inr hnil =>
          rw [hnil]
          show 1 + stf.length ≤ rest.length + 1
          rw [Nat.add_comm 1 stf.length]
          exact Nat.succ_le_succ hsl

/-- The quotient's carrier drops the divisor's own count: the
descent consumes one key per step, the below-top dividend leaving
the vacant quotient. -/
theorem div_quot_len (s P : Poly) :
    (div s P).1.length + s.length ≤ P.length ∨ (div s P).1 = [] := by
  have h := divGo_qlen P.length s.reverse P.reverse
  cases h with
  | inl hle =>
    refine Or.inl ?_
    show (divGo P.length s.reverse P.reverse).1.reverse.length + s.length
      ≤ P.length
    rw [ground.length_reverse (divGo P.length s.reverse P.reverse).1]
    rw [ground.length_reverse s, ground.length_reverse P] at hle
    exact hle
  | inr hnil =>
    refine Or.inr ?_
    show (divGo P.length s.reverse P.reverse).1.reverse = []
    rw [hnil]
    rfl

/-! The monomial kit, `def:poly`'s words at the member reads: the
monomial with its signed spelling, the geometric word, the pair at
one gap with its monic display and its split off the word, the
product's bilinearity over the sum fold, the monic cancellation
with its power corollary, and the signed-monomial fold read back at
its per-key coefficient counts. -/

/-- The monomial `t^n`. -/
def mono (n : Nat) : Poly := shiftUp n one

/-- The signed monomial: `t^n` on the stated side. -/
def smono (s : Bool) (n : Nat) : Poly :=
  shiftUp n [ground.signedAt s (BPair.ofPos .one)]

/-- The geometric word at a gap. -/
def gword (g : Nat) : Poly := List.replicate g (BPair.ofNat 1)

/-- The pair `<t^g : 1>`. -/
def tpair (g : Nat) : Poly := add (mono g) (neg one)

/-- A monomial multiplies as the shift, `mono_mul`'s one-sided
general. -/
theorem mono_mul_left : ∀ (c : Nat) (p : Poly),
    oneValue (mul (mono c) p) (shiftUp c p)
  | 0, p => one_mul p
  | c + 1, p => by
    show oneValue
      (add (p.map (fun d => BPair.unit * d))
        (BPair.unit :: mul (mono c) p))
      (BPair.unit :: shiftUp c p)
    exact oneValue_trans
      (unitTail_add
        (unitTail_scale (BPair.oneValue_refl BPair.unit) p) _)
      ⟨BPair.oneValue_refl _, mono_mul_left c p⟩

/-- Two monomials' product is the monomial at the joined key,
the one-sided read at a monomial argument. -/
theorem mono_mul (a b : Nat) :
    oneValue (mul (mono a) (mono b)) (mono (a + b)) := by
  refine oneValue_trans (mono_mul_left a (mono b)) ?_
  rw [show shiftUp a (mono b) = mono (a + b) from
    shiftUp_shiftUp a b one]
  exact oneValue_refl _

/-- The negation passes through the shift, the unit its own
partner. -/
theorem neg_shiftUp : ∀ (c : Nat) (p : Poly),
    neg (shiftUp c p) = shiftUp c (neg p)
  | 0, _ => rfl
  | c + 1, p => by
    show BPair.unit.swap :: neg (shiftUp c p) = BPair.unit :: _
    rw [neg_shiftUp c p]
    rfl

/-- The pair factor splits at the lower power: `⟨t^a : t^c⟩` is the
monomial at `c` against the pair at the gap. -/
theorem factor_split {c g a : Nat} (h : c + g = a) :
    oneValue (add (mono a) (neg (mono c)))
      (mul (mono c) (tpair g)) := by
  refine oneValue_symm (oneValue_trans (mono_mul_left c (tpair g)) ?_)
  show oneValue (shiftUp c (add (mono g) (neg one))) _
  refine oneValue_trans (shiftUp_add c (mono g) (neg one)) ?_
  rw [show shiftUp c (mono g) = mono (c + g) from
      shiftUp_shiftUp c g one,
    ← neg_shiftUp c one,
    show shiftUp c one = mono c from rfl, h]
  exact oneValue_refl _

/-- A product fold at monomial-scaled factors collects the
monomials' fold against the factors' own. -/
theorem mulFold_collect {α : Type} (c : α → Nat) (f : α → Poly) :
    ∀ l : List α,
    oneValue
      (ground.famFold mul one (fun q => mul (mono (c q)) (f q)) l)
      (mul (mono (ground.famFold Nat.add 0 c l))
        (ground.famFold mul one f l))
  | [] =>
    oneValue_symm (oneValue_trans (mul_comm (mono 0) one)
      (one_mul (mono 0)))
  | a :: l => by
    show oneValue
      (mul (mul (mono (c a)) (f a))
        (ground.famFold mul one (fun q => mul (mono (c q)) (f q)) l))
      (mul (mono (c a + ground.famFold Nat.add 0 c l))
        (mul (f a) (ground.famFold mul one f l)))
    refine oneValue_trans
      (mul_congr (mul (mono (c a)) (f a)) (mulFold_collect c f l)) ?_
    refine oneValue_trans
      (mul_exchange4 (mono (c a)) (f a)
        (mono (ground.famFold Nat.add 0 c l))
        (ground.famFold mul one f l)) ?_
    exact mul_congr_left (mono_mul (c a) _) _

/-- A monomial's Horner read at the natural one is the natural
one. -/
theorem eval_mono_one : ∀ n : Nat,
    (eval (mono n) (BPair.ofNat 1)).oneValue (BPair.ofNat 1)
  | 0 =>
    BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.mul_unit (BPair.ofNat 1)))
      (BPair.add_unit (BPair.ofPos .one))
  | n + 1 => by
    show (BPair.unit
        + BPair.ofNat 1 * eval (mono n) (BPair.ofNat 1)).oneValue
      (BPair.ofNat 1)
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _) (eval_mono_one n))
          (BPair.mul_ofNat_one (BPair.ofNat 1)))) ?_
    exact BPair.unit_add (BPair.ofNat 1)

/-- The product distributes over the sum fold, member by member. -/
theorem mul_famFold {α : Type} (f : α → Poly) :
    ∀ (l : List α) (q : Poly),
    oneValue (mul (ground.famFold add [] f l) q)
      (ground.famFold add [] (fun x => mul (f x) q) l)
  | [], _ => trivial
  | a :: t, q =>
    oneValue_trans (sum_mul (f a) (ground.famFold add [] f t) q)
      (add_congr (oneValue_refl _) (mul_famFold f t q))

/-- The geometric word's Horner read at the natural one counts the
letters. -/
theorem eval_gword_one : ∀ g : Nat,
    (eval (gword g) (BPair.ofNat 1)).oneValue (BPair.ofNat g)
  | 0 => BPair.oneValue_refl _
  | g + 1 => by
    show (BPair.ofNat 1
        + BPair.ofNat 1 * eval (gword g) (BPair.ofNat 1)).oneValue
      (BPair.ofNat (g + 1))
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _) (eval_gword_one g))
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq
              (BPair.mul_comm (BPair.ofNat 1) (BPair.ofNat g)))
            (BPair.mul_ofNat_one (BPair.ofNat g))))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.add_comm (BPair.ofNat 1) (BPair.ofNat g))) ?_
    exact BPair.oneValue_symm (BPair.ofNat_succ g)

/-- The geometric word's step: one more letter reads the word with
the next key's monomial. -/
private theorem gword_succ : ∀ g : Nat,
    oneValue (gword (g + 1)) (add (gword g) (mono g))
  | 0 => oneValue_refl _
  | g + 1 =>
    ⟨BPair.oneValue_symm (BPair.add_unit (BPair.ofNat 1)), gword_succ g⟩

/-- The pair at one gap against a monomial: the key raised, the
monomial's own copy swapped beside it. -/
private theorem tpair_mono (g : Nat) :
    oneValue (mul (tpair 1) (mono g))
      (add (mono (g + 1)) (neg (mono g))) := by
  refine oneValue_trans (sum_mul (mono 1) (neg one) (mono g))
    (add_congr ?_
      (oneValue_trans (neg_prod_left one (mono g))
        (swapMap_oneValue (one_mul (mono g)))))
  have h := mono_mul 1 g
  rw [Nat.add_comm 1 g] at h
  exact h

/-- The pair at a gap splits as the pair at one gap against the
geometric word, the telescoping read. -/
theorem tpair_split : ∀ g : Nat,
    oneValue (tpair (g + 1)) (mul (tpair 1) (gword (g + 1)))
  | 0 =>
    oneValue_symm
      (oneValue_trans (mul_comm (tpair 1) (gword 1)) (one_mul (tpair 1)))
  | g + 1 => by
    refine oneValue_symm ?_
    refine oneValue_trans (mul_congr (tpair 1) (gword_succ (g + 1))) ?_
    refine oneValue_trans
      (mul_sum (tpair 1) (gword (g + 1)) (mono (g + 1))) ?_
    refine oneValue_trans
      (add_congr (oneValue_symm (tpair_split g)) (tpair_mono (g + 1))) ?_
    refine oneValue_trans
      (add_congr (oneValue_refl (tpair (g + 1)))
        (add_comm (mono (g + 1 + 1)) (neg (mono (g + 1))))) ?_
    refine oneValue_trans
      (add_shuffle (mono (g + 1)) (neg one) (neg (mono (g + 1)))
        (mono (g + 1 + 1))) ?_
    refine oneValue_trans
      (unitTail_add (add_neg (mono (g + 1))) _) ?_
    exact add_comm (neg one) (mono (g + 1 + 1))

/-- The pair at one gap is the monic at the swapped scalar one. -/
theorem tpair_monic :
    oneValue (tpair 1) (monic [BPair.swap (BPair.ofPos .one)]) := by
  decide +kernel

/-- The shared monic right factor cancels: two products one value at
a monic read one value at their factors, the difference driven to
the unit tail through `monic_cancel`. -/
theorem mul_cancel_monic (s : Poly) {p q : Poly}
    (h : oneValue (mul p (monic s)) (mul q (monic s))) :
    oneValue p q := by
  have hd : unitTail (mul (add p (neg q)) (monic s)) :=
    oneValue_unitTail
      (oneValue_trans (sum_mul p (neg q) (monic s))
        (add_congr (oneValue_refl _) (neg_prod_left q (monic s))))
      (diff_unitTail h)
  exact ov_of_diff (monic_cancel (add p (neg q)).length s
    (add p (neg q)) [] (Nat.le_refl _) (Nat.zero_le _)
    (unitTail_oneValue
      (oneValue_unitTail (mul_comm (monic s) (add p (neg q))) hd)
      trivial))

/-- The monic power cancels, one factor peeled per step. -/
theorem powOf_cancel_monic (s : Poly) : ∀ (N : Nat) {p q : Poly},
    oneValue (mul p (powOf (monic s) N)) (mul q (powOf (monic s) N)) →
    oneValue p q
  | 0, p, q, h =>
    oneValue_trans
      (oneValue_symm (oneValue_trans (mul_comm p one) (one_mul p)))
      (oneValue_trans h (oneValue_trans (mul_comm q one) (one_mul q)))
  | N + 1, p, q, h => by
    have step : ∀ r : Poly,
        oneValue (mul r (powOf (monic s) (N + 1)))
          (mul (mul r (powOf (monic s) N)) (monic s)) := fun r =>
      oneValue_trans
        (mul_congr r (mul_comm (monic s) (powOf (monic s) N)))
        (oneValue_symm (mul_assoc r (powOf (monic s) N) (monic s)))
    exact powOf_cancel_monic s N
      (mul_cancel_monic s
        (oneValue_trans (oneValue_symm (step p))
          (oneValue_trans h (step q))))

/-- The signed monomial's entry at its own key. -/
private theorem getAt_smono_self (s : Bool) (n : Nat) :
    ground.getAt BPair.unit (smono s n) n
      = ground.signedAt s (BPair.ofPos .one) :=
  getAt_shiftUp_add n [ground.signedAt s (BPair.ofPos .one)] 0

/-- The signed monomial's entry off its key: the sum's unit. -/
private theorem getAt_smono_ne (s : Bool) {n k : Nat} (h : ¬ k = n) :
    ground.getAt BPair.unit (smono s n) k = BPair.unit := by
  cases Nat.lt_or_ge k n with
  | inl hlt => exact getAt_shiftUp_lt n _ k hlt
  | inr hge =>
    refine getAt_over BPair.unit _ k ?_
    have hl : (smono s n).length = n + 1 :=
      len_shift n [ground.signedAt s (BPair.ofPos .one)]
    rw [hl]
    exact Nat.lt_of_le_of_ne hge (fun e => h e.symm)

/-- The signed monomial's entry against the key pair's own count
read: the stated side's scalar one at its key, the unit off it. -/
private theorem smono_ofCounts (s : Bool) (n k : Nat) :
    (ground.getAt BPair.unit (smono s n) k).oneValue
      (BPair.ofCounts
        (if ((k, false) : Nat × Bool) = (n, s) then 1 else 0)
        (if ((k, true) : Nat × Bool) = (n, s) then 1 else 0)) := by
  by_cases hk : k = n
  · cases s with
    | false =>
      rw [hk, getAt_smono_self false n,
        if_pos (rfl : ((n, false) : Nat × Bool) = (n, false)),
        if_neg (fun e : ((n, true) : Nat × Bool) = (n, false) =>
          Bool.noConfusion (congrArg Prod.snd e))]
      exact BPair.oneValue_symm (BPair.add_unit (BPair.ofNat 1))
    | true =>
      rw [hk, getAt_smono_self true n,
        if_neg (fun e : ((n, false) : Nat × Bool) = (n, true) =>
          Bool.noConfusion (congrArg Prod.snd e)),
        if_pos (rfl : ((n, true) : Nat × Bool) = (n, true))]
      exact BPair.oneValue_symm (BPair.unit_add ((BPair.ofNat 1).swap))
  · rw [getAt_smono_ne s hk,
      if_neg (fun e : ((k, false) : Nat × Bool) = (n, s) =>
        hk (congrArg Prod.fst e)),
      if_neg (fun e : ((k, true) : Nat × Bool) = (n, s) =>
        hk (congrArg Prod.fst e))]
    exact BPair.oneValue_symm BPair.ofCounts_zero

/-- The signed-monomial fold's coefficient at a key is the key's
count pair, one grading side per count. -/
theorem monoFold_getAt {α : Type} (f : α → Nat) (sd : α → Bool) :
    ∀ (l : List α) (k : Nat),
    (ground.getAt BPair.unit
      (ground.famFold add [] (fun x => smono (sd x) (f x)) l)
      k).oneValue
    (BPair.ofCounts
      (ground.countOf (k, false) (l.map (fun x => (f x, sd x))))
      (ground.countOf (k, true) (l.map (fun x => (f x, sd x)))))
  | [], _ => BPair.oneValue_symm BPair.ofCounts_zero
  | a :: t, k => by
    show (ground.getAt BPair.unit
        (add (smono (sd a) (f a))
          (ground.famFold add [] (fun x => smono (sd x) (f x)) t))
        k).oneValue
      (BPair.ofCounts
        (ground.countOf (k, false)
          ((f a, sd a) :: t.map (fun x => (f x, sd x))))
        (ground.countOf (k, true)
          ((f a, sd a) :: t.map (fun x => (f x, sd x)))))
    rw [ground.countOf_cons, ground.countOf_cons]
    refine BPair.oneValue_trans (getAt_add _ _ k) ?_
    exact BPair.oneValue_trans
      (BPair.add_congr (smono_ofCounts (sd a) (f a) k)
        (monoFold_getAt f sd t k))
      (BPair.oneValue_symm (BPair.ofCounts_add _ _ _ _))

/-- Two signed-monomial folds at the crossed per-key balance read
one value, the graded folds' comparison shape. -/
theorem monoFold_ov {α β : Type} (f : α → Nat) (sd : α → Bool)
    (g : β → Nat) (se : β → Bool) (l : List α) (m : List β)
    (h : ∀ k : Nat,
      ground.countOf (k, false) (l.map (fun x => (f x, sd x)))
        + ground.countOf (k, true) (m.map (fun y => (g y, se y)))
      = ground.countOf (k, true) (l.map (fun x => (f x, sd x)))
        + ground.countOf (k, false) (m.map (fun y => (g y, se y)))) :
    oneValue (ground.famFold add [] (fun x => smono (sd x) (f x)) l)
      (ground.famFold add [] (fun y => smono (se y) (g y)) m) :=
  ov_of_getAt (fun k =>
    BPair.oneValue_trans (monoFold_getAt f sd l k)
      (BPair.oneValue_trans
        (BPair.ofCounts_crossed ((h k).trans (Nat.add_comm _ _)))
        (BPair.oneValue_symm (monoFold_getAt g se m k))))

/-! The signed folds' kit: the sum fold over a joined list, over a
flattened family, at one read per occupied member, and split over a
pointwise sum — the member reads' carrier at `def:poly`'s sum. -/

/-- The polynomial carrier's displayed sum at its one-value
relation, `def:poly`'s fold reads' bundle. -/
theorem polyFoldLaws : ground.FoldLaws Poly add [] oneValue where
  ovRefl := oneValue_refl
  ovSymm := oneValue_symm
  ovTrans := oneValue_trans
  opCongr := add_congr
  opComm := add_comm
  opAssoc := fun a b c => oneValue_symm (add_join a b c)
  unitOp := fun p => oneValue_refl p
  opUnit := fun p => oneValue_of_eq (add_nil p)

/-- The sum fold splits at a joined index list. -/
theorem foldP_append {α : Type} (E : α → Poly) :
    ∀ u v : List α,
    oneValue (ground.famFold add [] E (u ++ v))
      (add (ground.famFold add [] E u) (ground.famFold add [] E v)) :=
  ground.famFold_append_ov polyFoldLaws E

/-- The sum fold over a flattened family reads the fold of the
per-member folds. -/
theorem foldP_flatMap {α β : Type} (E : β → Poly) (g : α → List β) :
    ∀ l : List α,
    oneValue (ground.famFold add [] E (l.flatMap g))
      (ground.famFold add []
        (fun x => ground.famFold add [] E (g x)) l) :=
  ground.famFold_flatMap_ov polyFoldLaws E g

/-- Two sum folds at one read per occupied member are one value. -/
theorem foldP_congr_members {α : Type} [DecidableEq α]
    (E E' : α → Poly) : ∀ l : List α,
    (∀ x, 0 < ground.countOf x l → oneValue (E x) (E' x)) →
    oneValue (ground.famFold add [] E l)
      (ground.famFold add [] E' l) :=
  ground.famFold_congr_members_ov oneValue add [] oneValue_refl
    (fun h1 h2 => add_congr h1 h2) E E'

/-- The sum fold splits over a pointwise sum. -/
theorem foldP_add {α : Type} (E G : α → Poly) : ∀ l : List α,
    oneValue
      (ground.famFold add [] (fun x => add (E x) (G x)) l)
      (add (ground.famFold add [] E l) (ground.famFold add [] G l)) :=
  ground.famFold_add_ov polyFoldLaws E G

/-- The monomial's memberwise swap is the signed monomial at the
odd side. -/
theorem neg_mono : ∀ n : Nat, neg (mono n) = smono true n
  | 0 => rfl
  | n + 1 => by
    show BPair.unit :: neg (mono n) = BPair.unit :: smono true n
    rw [neg_mono n]

/-- A signed monomial scales a monomial to the joined key at its own
side. -/
theorem smono_mul_mono : ∀ (s : Bool) (a b : Nat),
    oneValue (mul (smono s a) (mono b)) (smono s (a + b))
  | false, a, b => mono_mul a b
  | true, a, b => by
    rw [← neg_mono a, ← neg_mono (a + b)]
    exact oneValue_trans (neg_prod_left (mono a) (mono b))
      (swapMap_oneValue (mono_mul a b))

/-- The pair product over an occupied-gap family collects the
unit-gap factors: one `<t:1>` per member against the geometric
words, the telescoping split taken at every factor. -/
theorem tpairFold_split {α : Type} [DecidableEq α]
    (g : α → Nat) : ∀ (l : List α),
    (∀ j, 0 < ground.countOf j l → 0 < g j) →
    oneValue
      (ground.famFold mul one (fun j => tpair (g j)) l)
      (mul (powOf (tpair 1) l.length)
        (ground.famFold mul one (fun j => gword (g j)) l))
  | [], _ =>
    oneValue_symm (oneValue_trans (mul_comm (powOf (tpair 1) 0) one)
      (one_mul (powOf (tpair 1) 0)))
  | a :: t, hpos => by
    have hta : ∀ j, 0 < ground.countOf j t → 0 < g j := fun j hj =>
      hpos j (Nat.lt_of_lt_of_le hj (Nat.le_add_left _ _))
    have hga : 0 < g a :=
      hpos a (by rw [ground.countOf_head]; exact Nat.succ_pos _)
    obtain ⟨m, hm⟩ : ∃ m, g a = m + 1 := by
      cases hc : g a with
      | zero => exact absurd (hc ▸ hga) (Nat.lt_irrefl 0)
      | succ m => exact ⟨m, rfl⟩
    show oneValue (mul (tpair (g a))
        (ground.famFold mul one (fun j => tpair (g j)) t))
      (mul (powOf (tpair 1) (t.length + 1))
        (mul (gword (g a))
          (ground.famFold mul one (fun j => gword (g j)) t)))
    have hsplit : oneValue (tpair (g a))
        (mul (tpair 1) (gword (g a))) := by
      rw [hm]
      exact tpair_split m
    refine oneValue_trans (mul_congr_left hsplit _) ?_
    refine oneValue_trans
      (mul_congr (mul (tpair 1) (gword (g a)))
        (tpairFold_split g t hta)) ?_
    refine oneValue_trans
      (mul_exchange4 (tpair 1) (gword (g a)) (powOf (tpair 1) t.length)
        (ground.famFold mul one (fun j => gword (g j)) t)) ?_
    exact oneValue_refl _

/-- The geometric words' product reads its gaps' product at the
natural one, the evaluation collecting the letters per factor. -/
theorem eval_gwordFold_one {α : Type} (g : α → Nat) :
    ∀ l : List α,
    (eval (ground.famFold mul one (fun j => gword (g j)) l)
      (BPair.ofNat 1)).oneValue
      (BPair.ofNat (ground.famFold Nat.mul 1 g l))
  | [] => eval_mono_one 0
  | a :: t => by
    show (eval (mul (gword (g a))
        (ground.famFold mul one (fun j => gword (g j)) t))
      (BPair.ofNat 1)).oneValue
      (BPair.ofNat (g a * ground.famFold Nat.mul 1 g t))
    refine BPair.oneValue_trans
      (eval_mul (gword (g a))
        (ground.famFold mul one (fun j => gword (g j)) t)
        (BPair.ofNat 1)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (eval_gword_one (g a))
        (eval_gwordFold_one g t)) ?_
    exact BPair.oneValue_symm
      (BPair.ofNat_mul (g a) (ground.famFold Nat.mul 1 g t))

/-! The iterated carrier: polynomials over the balance-pair
polynomials, `def:poly`'s displayed reads at the coefficient
carrier `def:elim`'s Sylvester tier names ("over the balance-pair
polynomials, a carrier with the displayed reads").  The sum adds
componentwise, the product convolves on the recursion, the
one-value read runs coefficientwise with tails against the sum's
unit, and the outer evaluation clears at a composite polynomial
point — `thm:trigpencil`'s symbol and the band-root substitution
the consumers, the variable names the consumers' own. -/

/-- A polynomial over the balance-pair polynomials: the total
coefficient list over the outer variable's monomial keys, each
coefficient a `Poly`. -/
abbrev PPoly := List Poly

/-- The sum adds componentwise over the outer keys, the longer
list's tail riding — the one recursion at the coefficient
carrier's bundle. -/
def padd : PPoly → PPoly → PPoly := addLO polyOps

/-- The product convolves on the recursion,
`(c + x P) Q = c Q + x (P Q)` — the one convolution at the
coefficient carrier's bundle. -/
def pmul : PPoly → PPoly → PPoly := mulLO polyOps

/-- The outer top key's coefficient, the vacant list at the
length-gauge tail. -/
def ptop : PPoly → Poly := topO polyOps

/-- The outer top is the entry at the outer list's last key. -/
theorem ptop_getAt (P : PPoly) (n : Nat) (h : P.length = n + 1) :
    ptop P = ground.getAt [] P n := topO_getAt polyOps P n h

/-- The negation read, the memberwise swap at every
coefficient. -/
def pnegP : PPoly → PPoly := (polyO polyOps).swap

/-- The representative list at every coefficient. -/
def pnormP (P : PPoly) : PPoly := P.map pnorm

/-- A pair of polynomials named as `def:ground`'s constructed pairs
are, the second member the positive datum's polynomial reading. -/
abbrev PPair := Poly × Poly

/-- The pairs' displayed sum, cross-multiplied. -/
def pAdd (x y : PPair) : PPair :=
  (add (mul x.1 y.2) (mul y.1 x.2), mul x.2 y.2)

/-- The pairs' displayed product. -/
def pMul (x y : PPair) : PPair :=
  (mul x.1 y.1, mul x.2 y.2)

/-- The sum's unit at the occupied second member. -/
def pZero : PPair := ([], one)

/-- The product's unit. -/
def pOne : PPair := (one, one)

/-- The memberwise swap at the first member, the negation read. -/
def pSwap (x : PPair) : PPair := (x.1.map ground.BPair.swap, x.2)

/-- The representative map memberwise. -/
def pnormPair (x : PPair) : PPair :=
  (x.1.map ground.BPair.norm, x.2.map ground.BPair.norm)

/-- The pair carrier's displayed operations, one bundle. -/
def ppairOps : DOps PPair := ⟨⟨pAdd, pMul, pZero, pOne⟩, pSwap⟩

/-- A cross read scales by one factor on each side. -/
theorem cross_scale {a b a' b' d d' : Poly}
    (h : oneValue (mul a b') (mul a' b)) :
    oneValue (mul (mul a d) (mul b' d'))
      (mul (mul a' d') (mul b d)) :=
  oneValue_trans (mul_exchange4 a d b' d')
    (oneValue_trans (mul_congr_left h (mul d d'))
      (oneValue_symm
        (oneValue_trans (mul_exchange4 a' d' b d)
          (mul_congr (mul a' b) (mul_comm d' d)))))

/-- The displayed sum's cross read at two stated cross reads, the
summands' calculus at the shared second data. -/
theorem pAdd_cross {x x' y y' : PPair}
    (h1 : oneValue (mul x.1 x'.2) (mul x'.1 x.2))
    (h2 : oneValue (mul y.1 y'.2) (mul y'.1 y.2)) :
    oneValue (mul (pAdd x y).1 (pAdd x' y').2)
      (mul (pAdd x' y').1 (pAdd x y).2) :=
  oneValue_trans
    (sum_mul (mul x.1 y.2) (mul y.1 x.2) (mul x'.2 y'.2))
    (oneValue_trans
      (add_congr
        (cross_scale h1)
        (oneValue_trans
          (mul_congr (mul y.1 x.2) (mul_comm x'.2 y'.2))
          (oneValue_trans (cross_scale h2)
            (mul_congr (mul y'.1 x'.2) (mul_comm y.2 x.2)))))
      (oneValue_symm
        (sum_mul (mul x'.1 y'.2) (mul y'.1 x'.2) (mul x.2 y.2))))

/-- The displayed product's cross read at two stated cross reads. -/
theorem pMul_cross {x x' y y' : PPair}
    (h1 : oneValue (mul x.1 x'.2) (mul x'.1 x.2))
    (h2 : oneValue (mul y.1 y'.2) (mul y'.1 y.2)) :
    oneValue (mul (pMul x y).1 (pMul x' y').2)
      (mul (pMul x' y').1 (pMul x y).2) :=
  oneValue_trans
    (mul_exchange4 x.1 y.1 x'.2 y'.2)
    (oneValue_trans
      (mul_congr_left h1 (mul y.1 y'.2))
      (oneValue_trans
        (mul_congr (mul x'.1 x.2) h2)
        (mul_exchange4 x'.1 x.2 y'.1 y.2)))

/-- The memberwise swap's cross read at a stated cross read. -/
theorem pSwap_cross {x y : PPair}
    (h : oneValue (mul x.1 y.2) (mul y.1 x.2)) :
    oneValue (mul (pSwap x).1 (pSwap y).2)
      (mul (pSwap y).1 (pSwap x).2) :=
  oneValue_trans (neg_prod_left x.1 y.2)
    (oneValue_trans (swapMap_oneValue h)
      (oneValue_symm (neg_prod_left y.1 x.2)))

/-- The polynomial carrier's own read bundle, the one-value read
with its decision — the tower's step at the balance-pair
entries. -/
def polyRead : DRead Poly := listRead bpairOps bpairRead

/-- Two lists read one value where every outer key's coefficients
do, a key beyond one list's top read against the sum's unit — the
one recursion at the coefficient carrier's read. -/
def ppOneValue : PPoly → PPoly → Prop := listOV polyOps polyRead

instance (P Q : PPoly) : Decidable (ppOneValue P Q) :=
  decListOV polyOps polyRead P Q

/-- The representative map reads its argument back at the iterated
carrier's one-value read, coefficient by coefficient. -/
theorem pnormP_ppOneValue : ∀ P : PPoly, ppOneValue (pnormP P) P
  | [] => trivial
  | c :: P => ⟨pnorm_oneValue c, pnormP_ppOneValue P⟩

/-- A tail's every suffix reads the tail, at any entry read. -/
theorem utDropO {γ : Type} (ops : DOps γ) (R : DRead γ) :
    ∀ (n : Nat) {p : List γ},
    unitTailO ops R p → unitTailO ops R (p.drop n)
  | 0, _, h => h
  | _ + 1, [], _ => trivial
  | n + 1, _ :: _, h => utDropO ops R n h.2

/-- A tail's every prefix reads the tail. -/
theorem utTakeO {γ : Type} (ops : DOps γ) (R : DRead γ) :
    ∀ (n : Nat) {p : List γ},
    unitTailO ops R p → unitTailO ops R (p.take n)
  | 0, _, _ => trivial
  | _ + 1, [], _ => trivial
  | n + 1, _ :: _, h => ⟨h.1, utTakeO ops R n h.2⟩

/-- A tail reads one value against the vacant list. -/
theorem lovNilO {γ : Type} (ops : DOps γ) (R : DRead γ) :
    ∀ {p : List γ}, unitTailO ops R p → listOV ops R p []
  | [], _ => trivial
  | _ :: _, h => h

/-- The vacant read is a tail. -/
theorem utOfNilO {γ : Type} (ops : DOps γ) (R : DRead γ) :
    ∀ {p : List γ}, listOV ops R p [] → unitTailO ops R p
  | [], _ => trivial
  | _ :: _, h => h

/-- The one-value read descends to matched suffixes. -/
theorem lovDropO {γ : Type} (ops : DOps γ) (R : DRead γ) :
    ∀ (n : Nat) {p q : List γ},
    listOV ops R p q → listOV ops R (p.drop n) (q.drop n)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | n + 1, [], _ :: _, h => utDropO ops R n h.2
  | n + 1, _ :: _, [], h => lovNilO ops R (utDropO ops R n h.2)
  | n + 1, _ :: _, _ :: _, h => lovDropO ops R n h.2

/-- The one-value read descends to matched prefixes. -/
theorem lovTakeO {γ : Type} (ops : DOps γ) (R : DRead γ) :
    ∀ (n : Nat) {p q : List γ},
    listOV ops R p q → listOV ops R (p.take n) (q.take n)
  | 0, _, _, _ => trivial
  | _ + 1, [], [], _ => trivial
  | n + 1, [], _ :: _, h => ⟨h.1, utTakeO ops R n h.2⟩
  | n + 1, _ :: _, [], h => ⟨h.1, utTakeO ops R n h.2⟩
  | n + 1, _ :: _, _ :: _, h => ⟨h.1, lovTakeO ops R n h.2⟩

/-- A tail whose every outer coefficient reads one value against
the sum's unit — the one recursion at the coefficient carrier's
read. -/
def ppUnitTail : PPoly → Prop := unitTailO polyOps polyRead

instance (P : PPoly) : Decidable (ppUnitTail P) :=
  decUnitTailO polyOps polyRead P

/-- The iterated one-value read pulls a unit tail back. -/
theorem ppOneValue_ppUnitTail : ∀ {P Q : PPoly},
    ppOneValue P Q → ppUnitTail Q → ppUnitTail P
  | [], _, _, _ => trivial
  | _ :: _, [], h, _ => h
  | _ :: _, _ :: _, h, hq =>
    ⟨oneValue_trans h.1 hq.1, ppOneValue_ppUnitTail h.2 hq.2⟩

/-- The iterated one-value read pushes a unit tail forward. -/
theorem ppUnitTail_ppOneValue_right : ∀ {Q S : PPoly},
    ppUnitTail Q → ppOneValue Q S → ppUnitTail S
  | [], _, _, h => h
  | _ :: _, [], _, _ => trivial
  | _ :: _, _ :: _, hq, h =>
    ⟨oneValue_trans (oneValue_symm h.1) hq.1,
     ppUnitTail_ppOneValue_right hq.2 h.2⟩

/-- The iterated one-value read's symmetry. -/
theorem ppOneValue_symm : ∀ {P Q : PPoly},
    ppOneValue P Q → ppOneValue Q P
  | [], [], h => h
  | [], _ :: _, h => h
  | _ :: _, [], h => h
  | _ :: _, _ :: _, h =>
    ⟨oneValue_symm h.1, ppOneValue_symm h.2⟩

/-- The iterated one-value read at every outer key: a key beyond a
top reads the vacant coefficient. -/
theorem ppOneValue_getAt : ∀ (k : Nat) {P Q : PPoly},
    ppOneValue P Q →
    oneValue (ground.getAt [] P k) (ground.getAt [] Q k)
  | 0, [], [], _ => trivial
  | 0, [], _ :: _, h => oneValue_symm h.1
  | 0, _ :: _, [], h => h.1
  | 0, _ :: _, _ :: _, h => h.1
  | _ + 1, [], [], _ => trivial
  | k + 1, [], _ :: _, h => ppOneValue_getAt k (P := []) h.2
  | k + 1, _ :: _, [], h =>
    ppOneValue_getAt k (lovNilO polyOps polyRead h.2)
  | k + 1, _ :: _, _ :: _, h => ppOneValue_getAt k h.2

/-- Two outer polynomials reading one value at occupied outer tops
read one value at the tops: the lists' lengths agree, a longer
list's top reading the shorter's vacant entry. -/
theorem ptop_congr : ∀ {P Q : PPoly}, ppOneValue P Q →
    ¬ unitTail (ptop P) → ¬ unitTail (ptop Q) → oneValue (ptop P) (ptop Q)
  | [], _, _, hP, _ => absurd trivial hP
  | _ :: _, [], _, _, hQ => absurd trivial hQ
  | c :: P, d :: Q, h, hP, hQ => by
    match Nat.lt_or_ge P.length Q.length with
    | .inl hlt =>
      have h1 := ppOneValue_getAt Q.length h
      rw [ground.getAt_over [] (c :: P) Q.length (Nat.succ_le_of_lt hlt),
        ← ptop_getAt (d :: Q) Q.length rfl] at h1
      exact absurd (oneValue_unitTail (oneValue_symm h1) trivial) hQ
    | .inr hge =>
      match Nat.lt_or_ge Q.length P.length with
      | .inl hgt =>
        have h1 := ppOneValue_getAt P.length h
        rw [ground.getAt_over [] (d :: Q) P.length (Nat.succ_le_of_lt hgt),
          ← ptop_getAt (c :: P) P.length rfl] at h1
        exact absurd (oneValue_unitTail h1 trivial) hP
      | .inr hle =>
        have heq : P.length = Q.length := Nat.le_antisymm hle hge
        rw [ptop_getAt (c :: P) P.length rfl,
          ptop_getAt (d :: Q) P.length (congrArg Nat.succ heq.symm)]
        exact ppOneValue_getAt P.length h

/-- A scale of the sum's unit reads it back. -/
private theorem scale_unit_read (w : Pos) {a : BPair}
    (h : a.oneValue BPair.unit) :
    (a.scale w).oneValue BPair.unit :=
  BPair.oneValue_trans (BPair.scale_congr w h)
    (BPair.oneValue_symm (ground.unitScale w))

/-- The entrywise scale keeps a unit tail. -/
private theorem unitTail_mapScale (w : Pos) : ∀ {p : Poly},
    unitTail p → unitTail (p.map (fun x => x.scale w))
  | [], _ => trivial
  | _ :: _, h => ⟨scale_unit_read w h.1, unitTail_mapScale w h.2⟩

/-- The entrywise scale moves across the one-value read. -/
theorem mapScale_congr (w : Pos) : ∀ {p q : Poly},
    oneValue p q →
    oneValue (p.map (fun x => x.scale w)) (q.map (fun x => x.scale w))
  | [], _, h => unitTail_mapScale w h
  | _ :: _, [], h => ⟨scale_unit_read w h.1, unitTail_mapScale w h.2⟩
  | _ :: _, _ :: _, h =>
    ⟨BPair.scale_congr w h.1, mapScale_congr w h.2⟩

/-- The evaluation of a memberwise rescaled list is the evaluation
rescaled. -/
private theorem mapScale_ov (c : Pos) : ∀ P : Poly,
    oneValue (P.map (fun x => x.scale c))
      (P.map (fun d => BPair.ofPos c * d))
  | [] => trivial
  | y :: t =>
    And.intro (BPair.oneValue_symm (BPair.ofPos_scale c y))
      (mapScale_ov c t)

theorem eval_mapScale (P : Poly) (c : Pos) (x : BPair) :
    (eval (P.map (fun y => y.scale c)) x).oneValue
      ((eval P x).scale c) :=
  BPair.oneValue_trans (eval_congr (mapScale_ov c P) x)
    (BPair.oneValue_trans (eval_scale P (BPair.ofPos c) x)
      (BPair.ofPos_scale c (eval P x)))

/-- The shifted derivative keeps a unit tail. -/
private theorem unitTail_derivFrom : ∀ (n : Pos) {p : Poly},
    unitTail p → unitTail (derivFrom n p)
  | _, [], _ => trivial
  | n, _ :: _, h =>
    ⟨scale_unit_read n h.1, unitTail_derivFrom (succ n) h.2⟩

/-- The shifted derivative moves across the one-value read. -/
private theorem derivFrom_congr : ∀ (n : Pos) {p q : Poly},
    oneValue p q → oneValue (derivFrom n p) (derivFrom n q)
  | _, [], _, h => unitTail_derivFrom _ h
  | n, _ :: _, [], h =>
    ⟨scale_unit_read n h.1, unitTail_derivFrom (succ n) h.2⟩
  | n, _ :: _, _ :: _, h =>
    ⟨BPair.scale_congr n h.1, derivFrom_congr (succ n) h.2⟩

/-- The derivative moves across the one-value read: the
successor-weighted shift at matched keys. -/
theorem deriv_congr : ∀ {p q : Poly},
    oneValue p q → oneValue (deriv p) (deriv q)
  | [], [], _ => trivial
  | [], _ :: _, h => unitTail_derivFrom .one h.2
  | _ :: _, [], h =>
    lovNilO bpairOps bpairRead (unitTail_derivFrom .one h.2)
  | _ :: _, _ :: _, h => derivFrom_congr .one h.2

/-- The outer evaluation at a composite polynomial point, cleared
at the shared power: `Σ_k P_k q^k c^(K-k)`, the coefficient
carrier's own Horner shape — `evalClear` at a one-member point,
the band-root substitution at the cleared root identity; the
coefficientwise evaluation at a base point (`pevalB`) reads the
outer sum and product as the sum and product and passes the outer
one-value read. -/
def pevalC (P : PPoly) (q : Poly) (c : Pos) (K : Nat) : Poly :=
  (List.range P.length).foldl (fun a k =>
    add a (pnorm (scaleP (BPair.ofPos (Pos.powC c (K - k)))
      (mul (ground.getAt [] P k) (powOf q k))))) []

/-- The outer evaluation at the unit clearing collects to the
monomial fold: the clearing's powers withdraw, leaving the
coefficient against the outer point's power, key by key. -/
theorem pevalC_fold (P : PPoly) (q : Poly) (K : Nat) :
    oneValue (pevalC P q Pos.one K)
      (ground.famFold add []
        (fun k => mul (ground.getAt [] P k) (powOf q k))
        (List.range P.length)) := by
  refine oneValue_trans
    (ground.foldlFamO polyFoldLaws
      (fun k => pnorm (scaleP (BPair.ofPos (Pos.powC Pos.one (K - k)))
        (mul (ground.getAt [] P k) (powOf q k))))
      (List.range P.length) []) ?_
  refine oneValue_trans (polyFoldLaws.unitOp _) ?_
  refine ground.famFold_congr_members_ov oneValue add []
    oneValue_refl (fun h1 h2 => add_congr h1 h2) _ _
    (List.range P.length) (fun k _ => ?_)
  rw [Pos.powC_one]
  exact oneValue_trans (pnorm_oneValue _) (scaleP_one _)

/-- The monic linear factor at a located root, `z` against the
root's value. -/
def linFacM (r : BPair) : Poly := [r.swap, BPair.ofPos .one]

private def multGo : Nat → Poly → Poly → Nat
  | 0, _, _ => 0
  | fuel + 1, s, P =>
    if @decide (unitTail (div s P).2) (decUnitTail _)
    then multGo fuel s (div s P).1 + 1
    else 0

/-- The multiplicity by iterated divisions at a monic factor,
entered as its below-top list. -/
def multAt (s P : Poly) : Nat := multGo P.length s P

/-! `def:poly`'s multiplicity at a located root: the count of
iterated divisions there, its factorization read with the
uniqueness, and the reads of the count at a product, at a root and
at the derivative. -/

/-- The monic linear factor is occupied: its top is the scalar
one. -/
theorem linFacM_occupied (r : BPair) : ¬ unitTail (linFacM r) :=
  fun h => ground.BPair.ofPos_off Pos.one h.2.1

/-- The monic linear factor's own root: the Horner read at the
located value is the two members' join. -/
theorem isRoot_linFacM (r : BPair) : isRoot (linFacM r) r :=
  eval_monic_linear r.swap

/-- The monic linear factor's Horner read at a value is the value
against the root's balance partner. -/
theorem eval_linFacM (r x : BPair) :
    (eval (linFacM r) x).oneValue (x + r.swap) := by
  have t1 : (eval [BPair.ofPos Pos.one] x).oneValue (BPair.ofPos Pos.one) :=
    eval_one (BPair.ofPos Pos.one) x
  have t2 : (x * eval [BPair.ofPos Pos.one] x).oneValue x :=
    BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl x) t1)
      (ground.BPair.mul_one_read x)
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl r.swap) t2)
    (BPair.oneValue_of_eq (BPair.add_comm r.swap x))

private theorem multGo_pos (fuel : Nat) (s P : Poly)
    (h : unitTail (div s P).2) :
    multGo (fuel + 1) s P = multGo fuel s (div s P).1 + 1 := by
  show (if @decide (unitTail (div s P).2) (decUnitTail _)
      then multGo fuel s (div s P).1 + 1 else 0)
    = multGo fuel s (div s P).1 + 1
  cases hd : @decide (unitTail (div s P).2)
      (decUnitTail _) with
  | true => rfl
  | false => exact absurd h (of_decide_eq_false hd)

private theorem multGo_null (fuel : Nat) (s P : Poly)
    (h : ¬ unitTail (div s P).2) :
    multGo (fuel + 1) s P = 0 := by
  show (if @decide (unitTail (div s P).2) (decUnitTail _)
      then multGo fuel s (div s P).1 + 1 else 0) = 0
  cases hd : @decide (unitTail (div s P).2)
      (decUnitTail _) with
  | true => exact absurd (of_decide_eq_true hd) h
  | false => rfl

/-- A stated factorization at the linear factor's power leaves the
dividend occupied: the power and the root-free cofactor both sit off
the sum's unit, and the product with them. -/
private theorem occupied_of_factor (r : BPair) (P Q : Poly) (m : Nat)
    (h : oneValue P (mul (powOf (linFacM r) m) Q))
    (hQ : ¬ isRoot Q r) : ¬ unitTail P := fun hu =>
  (unitTail_mul_of (unitTail_oneValue_right hu h)).elim
    (powOf_occupied (linFacM_occupied r) m)
    (fun hq => hQ (eval_congr
      (unitTail_oneValue hq
        (show unitTail ([] : Poly) from trivial)) r))

/-- The fuel read at the descent: each exact division drops the
dividend's carrier by the divisor's own count, so a fuel at the
dividend's carrier clears the count. -/
private theorem multGo_read : ∀ (fuel : Nat) (r : BPair) (P : Poly),
    ¬ unitTail P → P.length ≤ fuel →
    ∃ Q : Poly, oneValue P
        (mul (powOf (linFacM r) (multGo fuel [r.swap] P)) Q)
      ∧ ¬ isRoot Q r
  | 0, _, [], hP, _ => absurd trivial hP
  | 0, _, _ :: _, _, hf => absurd hf (Nat.not_succ_le_zero _)
  | fuel + 1, r, P, hP, hf => by
    by_cases hrem : unitTail (div [r.swap] P).2
    · rw [multGo_pos fuel [r.swap] P hrem]
      have hid : oneValue P
          (mul (monic [r.swap]) (div [r.swap] P).1) :=
        oneValue_symm
          (oneValue_trans
            (oneValue_symm
              (add_unitTail
                (mul (monic [r.swap]) (div [r.swap] P).1)
                hrem))
            (div_identity [r.swap] P))
      have hP' : ¬ unitTail (div [r.swap] P).1 := fun hu =>
        hP (oneValue_unitTail hid
          (mul_unitTail (monic [r.swap]) hu))
      have hlen : (div [r.swap] P).1.length ≤ fuel := by
        cases div_quot_len [r.swap] P with
        | inl hle => exact Nat.le_of_succ_le_succ (Nat.le_trans hle hf)
        | inr hnil =>
          rw [hnil]
          exact Nat.zero_le _
      obtain ⟨Q, hQ1, hQ2⟩ :=
        multGo_read fuel r (div [r.swap] P).1 hP' hlen
      refine ⟨Q, ?_, hQ2⟩
      refine oneValue_trans hid ?_
      refine oneValue_trans
        (mul_congr (monic [r.swap]) hQ1) ?_
      exact oneValue_symm
        (mul_assoc (linFacM r)
          (powOf (linFacM r)
            (multGo fuel [r.swap] (div [r.swap] P).1))
          Q)
    · rw [multGo_null fuel [r.swap] P hrem]
      refine ⟨P, oneValue_symm (one_mul P), fun hroot => ?_⟩
      exact hrem (unitTail_oneValue_right
        (show unitTail [eval P r] from ⟨hroot, trivial⟩)
        (oneValue_symm (div_linear_eval r.swap P)))

/-- The multiplicity's factorization read: at an occupied dividend
the count of iterated divisions at the root splits the polynomial as
that power of the linear factor against a cofactor off the root. -/
theorem multAt_read (r : BPair) (P : Poly)
    (hP : ¬ unitTail P) :
    ∃ Q : Poly, oneValue P
        (mul (powOf (linFacM r) (multAt [r.swap] P)) Q)
      ∧ ¬ isRoot Q r :=
  multGo_read P.length r P hP (Nat.le_refl _)

private theorem multGo_of : ∀ (fuel : Nat) (r : BPair) (P Q : Poly)
    (m : Nat), P.length ≤ fuel →
    oneValue P (mul (powOf (linFacM r) m) Q) →
    ¬ isRoot Q r → multGo fuel [r.swap] P = m
  | 0, r, [], Q, m, _, h, hQ2 =>
    absurd trivial (occupied_of_factor r [] Q m h hQ2)
  | 0, _, _ :: _, _, _, hf, _, _ => absurd hf (Nat.not_succ_le_zero _)
  | fuel + 1, r, P, Q, m, hf, h, hQ2 => by
    match m with
    | 0 =>
      have hPQ : oneValue P Q :=
        oneValue_trans h (one_mul Q)
      refine multGo_null fuel [r.swap] P (fun hu => ?_)
      exact hQ2 (isRoot_congr hPQ
        (unitTail_oneValue_right hu
          (div_linear_eval r.swap P)).1)
    | k + 1 =>
      have hunit : unitTail [BPair.unit] :=
        ⟨ground.BPair.oneValue_refl _, trivial⟩
      have hstep : oneValue
          (add (mul (monic [r.swap])
            (mul (powOf (linFacM r) k) Q)) [BPair.unit]) P := by
        refine oneValue_trans (add_unitTail _ hunit) ?_
        refine oneValue_symm (oneValue_trans h ?_)
        exact mul_assoc (linFacM r) (powOf (linFacM r) k) Q
      obtain ⟨hq1, hr1⟩ := div_unique [r.swap] P
        (mul (powOf (linFacM r) k) Q) [BPair.unit] rfl hstep
      rw [multGo_pos fuel [r.swap] P
        (unitTail_oneValue_right hunit hr1)]
      have hIH : multGo fuel [r.swap] (div [r.swap] P).1 = k := by
        refine multGo_of fuel r (div [r.swap] P).1 Q k ?_
          (oneValue_symm hq1) hQ2
        cases div_quot_len [r.swap] P with
        | inl hle => exact Nat.le_of_succ_le_succ (Nat.le_trans hle hf)
        | inr hnil =>
          rw [hnil]
          exact Nat.zero_le _
      rw [hIH]

/-- The multiplicity's uniqueness: the division at a monic is unique
and a root-free cofactor refuses one more division, so a stated
factorization names the count. -/
theorem multAt_of (r : BPair) (P Q : Poly) (m : Nat)
    (h : oneValue P (mul (powOf (linFacM r) m) Q))
    (hQ : ¬ isRoot Q r) : multAt [r.swap] P = m :=
  multGo_of P.length r P Q m (Nat.le_refl _) h hQ

/-- The count adds over a product of occupied factors. -/
theorem multAt_mul (r : BPair) (P Q : Poly)
    (hP : ¬ unitTail P) (hQ : ¬ unitTail Q) :
    multAt [r.swap] (mul P Q)
      = multAt [r.swap] P + multAt [r.swap] Q := by
  obtain ⟨A, hA1, hA2⟩ := multAt_read r P hP
  obtain ⟨B, hB1, hB2⟩ := multAt_read r Q hQ
  refine multAt_of r (mul P Q) (mul A B)
    (multAt [r.swap] P + multAt [r.swap] Q) ?_
    (fun hr => ((isRoot_mul A B r).mp hr).elim hA2 hB2)
  refine oneValue_trans
    (oneValue_trans (mul_congr_left hA1 Q)
      (mul_congr _ hB1)) ?_
  refine oneValue_trans
    (mul_exchange4 (powOf (linFacM r) (multAt [r.swap] P)) A
      (powOf (linFacM r) (multAt [r.swap] Q)) B) ?_
  exact mul_congr_left
    (oneValue_symm
      (powOf_add (linFacM r) (multAt [r.swap] P) (multAt [r.swap] Q)))
    (mul A B)

/-- A located root is exactly an occupied count. -/
theorem multAt_pos (r : BPair) (P : Poly)
    (hP : ¬ unitTail P) :
    isRoot P r ↔ 0 < multAt [r.swap] P := by
  obtain ⟨Q, hQ1, hQ2⟩ := multAt_read r P hP
  constructor
  · intro hr
    cases hm : multAt [r.swap] P with
    | zero =>
      rw [hm] at hQ1
      exact absurd
        (isRoot_congr (oneValue_trans hQ1 (one_mul Q)) hr)
        hQ2
    | succ k => exact Nat.succ_pos k
  · intro hpos
    cases hm : multAt [r.swap] P with
    | zero =>
      rw [hm] at hpos
      exact absurd hpos (Nat.lt_irrefl 0)
    | succ k =>
      rw [hm] at hQ1
      refine isRoot_congr (oneValue_symm hQ1) ?_
      refine (isRoot_mul _ Q r).mpr (Or.inl ?_)
      exact (isRoot_powOf (linFacM r) r (k + 1)
        (Nat.succ_pos k)).mpr (isRoot_linFacM r)

/-- A repeated root is a root of the derivative: the Leibniz rule
splits the stated factorization, the power's own derivative keeping
one linear factor at a count from two. -/
theorem multAt_deriv (r : BPair) (P : Poly)
    (hP : ¬ unitTail P) (h2 : 2 ≤ multAt [r.swap] P) :
    isRoot (deriv P) r := by
  obtain ⟨Q, hQ1, _⟩ := multAt_read r P hP
  obtain ⟨k, hk⟩ := Nat.le.dest h2
  have hk2 : multAt [r.swap] P = k + 2 := by
    rw [← hk]
    exact Nat.add_comm 2 k
  rw [hk2] at hQ1
  have hL : isRoot (linFacM r) r := isRoot_linFacM r
  have hpk : isRoot (powOf (linFacM r) (k + 1)) r :=
    (isRoot_powOf (linFacM r) r (k + 1) (Nat.succ_pos k)).mpr hL
  have hdA : isRoot
      (deriv (powOf (linFacM r) (k + 2))) r := by
    refine isRoot_congr (oneValue_symm
      (deriv_mul (linFacM r) (powOf (linFacM r) (k + 1)))) ?_
    refine isRoot_add ?_ ?_
    · exact (isRoot_mul (deriv (linFacM r))
        (powOf (linFacM r) (k + 1)) r).mpr (Or.inr hpk)
    · exact (isRoot_mul (linFacM r)
        (deriv (powOf (linFacM r) (k + 1))) r).mpr (Or.inl hL)
  refine isRoot_congr
    (oneValue_symm (deriv_congr hQ1)) ?_
  refine isRoot_congr (oneValue_symm
    (deriv_mul (powOf (linFacM r) (k + 2)) Q)) ?_
  refine isRoot_add ?_ ?_
  · exact (isRoot_mul (deriv (powOf (linFacM r) (k + 2)))
      Q r).mpr (Or.inl hdA)
  · exact (isRoot_mul (powOf (linFacM r) (k + 2))
      (deriv Q) r).mpr
      (Or.inl ((isRoot_powOf (linFacM r) r (k + 2)
        (Nat.succ_pos _)).mpr hL))

/-- The multiplicity is a class read: two polynomials at one value
read one count. -/
theorem multAt_congr (r : BPair) {P P' : Poly}
    (h : oneValue P P') (hP : ¬ unitTail P) :
    multAt [r.swap] P = multAt [r.swap] P' := by
  obtain ⟨Q, hQ, hr⟩ := multAt_read r P hP
  exact (multAt_of r P' Q _ (oneValue_trans (oneValue_symm h) hQ)
    hr).symm

/-- The power's multiplicity is the count's multiple. -/
theorem multAt_powOf (r : BPair) (P : Poly)
    (hP : ¬ unitTail P) : ∀ n : Nat,
    multAt [r.swap] (powOf P n) = n * multAt [r.swap] P
  | 0 => by
    rw [Nat.zero_mul]
    exact multAt_of r _ one 0
      (oneValue_symm (one_mul one)) (isRoot_one r)
  | n + 1 => by
    show multAt [r.swap] (mul P (powOf P n)) = _
    rw [multAt_mul r P _ hP (powOf_occupied hP n), multAt_powOf r P hP n,
      Nat.succ_mul, Nat.add_comm]

/-- The outer polynomial evaluated at a base point coefficientwise:
each coefficient's Horner read, the result a polynomial in the outer
variable over the pairs. -/
def pevalB (P : PPoly) (t : BPair) : Poly := P.map (fun c => eval c t)

/-- The evaluation reads the outer sum as the sum. -/
theorem pevalB_padd : ∀ (P Q : PPoly) (t : BPair),
    oneValue (pevalB (padd P Q) t) (add (pevalB P t) (pevalB Q t))
  | [], _, _ => oneValue_refl _
  | _ :: _, [], _ => oneValue_refl _
  | c :: P, d :: Q, t =>
    ⟨eval_add c d t, pevalB_padd P Q t⟩

/-- The evaluation reads the outer product as the product. -/
theorem pevalB_pmul : ∀ (P Q : PPoly) (t : BPair),
    oneValue (pevalB (pmul P Q) t) (mul (pevalB P t) (pevalB Q t))
  | [], _, _ => trivial
  | c :: P, Q, t => by
    show oneValue (pevalB (padd (Q.map (mul c)) ([] :: pmul P Q)) t)
      (add ((Q.map (fun d => eval d t)).map (fun x => eval c t * x))
        (BPair.unit :: mul (pevalB P t) (pevalB Q t)))
    refine oneValue_trans (pevalB_padd _ _ t) ?_
    refine add_congr ?_ ⟨BPair.oneValue_refl _, pevalB_pmul P Q t⟩
    show oneValue ((Q.map (mul c)).map (fun d => eval d t))
      ((Q.map (fun d => eval d t)).map (fun x => eval c t * x))
    rw [ground.map_map, ground.map_map]
    exact oneValue_map _ _ Q (fun d _ => eval_mul c d t)

/-- A unit-tailed outer polynomial evaluates to a unit tail. -/
theorem pevalB_ppUnitTail (t : BPair) : ∀ {P : PPoly}, ppUnitTail P →
    unitTail (pevalB P t)
  | [], _ => trivial
  | _ :: _, h => ⟨eval_congr h.1 t, pevalB_ppUnitTail t h.2⟩

/-- The coefficientwise evaluation passes the outer one-value read. -/
theorem pevalB_congr (t : BPair) : ∀ {P Q : PPoly}, ppOneValue P Q →
    oneValue (pevalB P t) (pevalB Q t)
  | [], _, h => pevalB_ppUnitTail t h
  | _ :: _, [], h => ⟨eval_congr h.1 t, pevalB_ppUnitTail t h.2⟩
  | _ :: _, _ :: _, h => ⟨eval_congr h.1 t, pevalB_congr t h.2⟩

/-- The evaluated outer polynomial's top is the outer top's
evaluation, the coefficientwise map keeping the length gauge. -/
theorem top_pevalB : ∀ (P : PPoly) (t : BPair),
    top (pevalB P t) = eval (ptop P) t
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: c :: P, t => top_pevalB (c :: P) t

end poly
